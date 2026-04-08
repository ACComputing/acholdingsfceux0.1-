#!/usr/bin/env python3
# cython: language_level=3
"""
AC HOLDINGS NES EMU 2.0 - FULL PPU NATIVE CORE
(C) 1999-2026 A.C Holdings / Team Flames

A complete NES emulator with full PPU scanline rendering,
expanded 6502 CPU (all official opcodes), sprite engine,
nametable scrolling, palette RAM, NMI, sprite-0 hit,
and keyboard-mapped controller input.

Single-file Python + Tkinter. No external deps.
"""

import tkinter as tk
from tkinter import filedialog, messagebox
import os, time

# ============================================================
# NES MASTER PALETTE (64 entries, RGB tuples)
# ============================================================
NES_PALETTE = [
    (84,84,84),(0,30,116),(8,16,144),(48,0,136),
    (68,0,100),(92,0,48),(84,4,0),(60,24,0),
    (32,42,0),(8,58,0),(0,64,0),(0,60,0),
    (0,50,60),(0,0,0),(0,0,0),(0,0,0),
    (152,150,152),(8,76,196),(48,50,236),(92,30,228),
    (136,20,176),(160,20,100),(152,34,32),(120,60,0),
    (84,90,0),(40,114,0),(8,124,0),(0,118,40),
    (0,102,120),(0,0,0),(0,0,0),(0,0,0),
    (236,238,236),(76,154,236),(120,124,236),(176,98,236),
    (228,84,236),(236,88,180),(236,106,100),(212,136,32),
    (160,170,0),(116,196,0),(76,208,32),(56,204,108),
    (56,180,204),(60,60,60),(0,0,0),(0,0,0),
    (236,238,236),(168,204,236),(188,188,236),(212,178,236),
    (236,174,236),(236,174,212),(236,180,176),(228,196,144),
    (204,210,120),(180,222,120),(168,226,144),(152,226,180),
    (160,214,228),(160,162,160),(0,0,0),(0,0,0),
]

# Pre-compute hex color strings for PhotoImage
NES_HEX = [f"#{r:02x}{g:02x}{b:02x}" for r, g, b in NES_PALETTE]


# ============================================================
# PPU - Picture Processing Unit
# ============================================================
class PPU:
    def __init__(self):
        # PPU Memory
        self.chr_rom = bytearray(0x2000)   # 8KB Pattern tables (CHR ROM/RAM)
        self.chr_ram_mode = False
        self.vram = bytearray(0x0800)      # 2KB Nametable RAM
        self.palette_ram = bytearray(32)   # Palette RAM
        self.oam = bytearray(256)          # Primary OAM
        self.secondary_oam = bytearray(32) # 8 sprites per scanline

        # Registers
        self.ppuctrl = 0    # $2000
        self.ppumask = 0    # $2001
        self.ppustatus = 0  # $2002
        self.oamaddr = 0    # $2003

        # Loopy internal registers
        self.v = 0          # Current VRAM address (15-bit)
        self.t = 0          # Temp VRAM address (15-bit)
        self.fine_x = 0     # Fine X scroll (3-bit)
        self.w = 0          # Write toggle (1-bit)

        # $2007 read buffer
        self.data_buffer = 0

        # Mirroring: 0=horizontal, 1=vertical
        self.mirroring = 0

        # Rendering state
        self.scanline = 0
        self.cycle = 0
        self.frame_count = 0
        self.odd_frame = False

        # Frame buffer: 256x240 palette indices → converted at display time
        self.framebuffer = bytearray(256 * 240)

        # NMI control
        self.nmi_occurred = False
        self.nmi_output = False
        self.suppress_nmi = False

        # Sprite-0 hit
        self.sprite_zero_hit = False
        self.sprite_zero_on_line = False

        # Background shift registers & latches (per-scanline rendering)
        self._bg_next_tile_id = 0
        self._bg_next_attr = 0
        self._bg_next_lo = 0
        self._bg_next_hi = 0
        self._bg_shift_pat_lo = 0
        self._bg_shift_pat_hi = 0
        self._bg_shift_attr_lo = 0
        self._bg_shift_attr_hi = 0

        # Sprite rendering buffers
        self._sprite_count = 0
        self._sprite_patterns_lo = [0] * 8
        self._sprite_patterns_hi = [0] * 8
        self._sprite_positions = [0] * 8
        self._sprite_priorities = [0] * 8
        self._sprite_indices = [0] * 8

    # ---- PPU Memory Access ----
    def _mirror_nametable(self, addr):
        """Apply nametable mirroring to get VRAM offset."""
        addr &= 0x0FFF
        if self.mirroring == 1:  # Vertical
            return addr & 0x07FF
        else:  # Horizontal
            if addr < 0x0400:
                return addr
            elif addr < 0x0800:
                return addr - 0x0400
            elif addr < 0x0C00:
                return addr - 0x0400
            else:
                return addr - 0x0800

    def ppu_read(self, addr):
        addr &= 0x3FFF
        if addr < 0x2000:
            return self.chr_rom[addr & 0x1FFF]
        elif addr < 0x3F00:
            return self.vram[self._mirror_nametable(addr - 0x2000)]
        else:
            pa = addr & 0x1F
            if pa == 0x10: pa = 0x00
            if pa == 0x14: pa = 0x04
            if pa == 0x18: pa = 0x08
            if pa == 0x1C: pa = 0x0C
            return self.palette_ram[pa] & (0x30 if (self.ppumask & 0x01) else 0x3F)

    def ppu_write(self, addr, val):
        addr &= 0x3FFF
        val &= 0xFF
        if addr < 0x2000:
            if self.chr_ram_mode:
                self.chr_rom[addr & 0x1FFF] = val
        elif addr < 0x3F00:
            self.vram[self._mirror_nametable(addr - 0x2000)] = val
        else:
            pa = addr & 0x1F
            if pa == 0x10: pa = 0x00
            if pa == 0x14: pa = 0x04
            if pa == 0x18: pa = 0x08
            if pa == 0x1C: pa = 0x0C
            self.palette_ram[pa] = val

    # ---- CPU-facing register interface ----
    def cpu_read(self, reg):
        """Read PPU register (reg = 0-7 for $2000-$2007)."""
        if reg == 2:  # PPUSTATUS
            val = (self.ppustatus & 0xE0) | (self.data_buffer & 0x1F)
            self.ppustatus &= ~0x80  # Clear vblank
            self.nmi_occurred = False
            self.w = 0
            return val
        elif reg == 4:  # OAMDATA
            return self.oam[self.oamaddr]
        elif reg == 7:  # PPUDATA
            addr = self.v & 0x3FFF
            val = self.data_buffer
            self.data_buffer = self.ppu_read(addr)
            if addr >= 0x3F00:
                val = self.data_buffer
                self.data_buffer = self.ppu_read(addr - 0x1000)
            self.v = (self.v + (32 if (self.ppuctrl & 0x04) else 1)) & 0x7FFF
            return val
        return 0

    def cpu_write(self, reg, val):
        """Write PPU register."""
        val &= 0xFF
        if reg == 0:  # PPUCTRL
            self.ppuctrl = val
            self.nmi_output = bool(val & 0x80)
            self.t = (self.t & 0xF3FF) | ((val & 0x03) << 10)
        elif reg == 1:  # PPUMASK
            self.ppumask = val
        elif reg == 3:  # OAMADDR
            self.oamaddr = val
        elif reg == 4:  # OAMDATA
            self.oam[self.oamaddr] = val
            self.oamaddr = (self.oamaddr + 1) & 0xFF
        elif reg == 5:  # PPUSCROLL
            if self.w == 0:
                self.fine_x = val & 0x07
                self.t = (self.t & 0xFFE0) | (val >> 3)
                self.w = 1
            else:
                self.t = (self.t & 0x8C1F) | ((val & 0x07) << 12) | ((val & 0xF8) << 2)
                self.w = 0
        elif reg == 6:  # PPUADDR
            if self.w == 0:
                self.t = (self.t & 0x00FF) | ((val & 0x3F) << 8)
                self.w = 1
            else:
                self.t = (self.t & 0xFF00) | val
                self.v = self.t
                self.w = 0
        elif reg == 7:  # PPUDATA
            self.ppu_write(self.v & 0x3FFF, val)
            self.v = (self.v + (32 if (self.ppuctrl & 0x04) else 1)) & 0x7FFF

    # ---- Rendering helpers ----
    def _rendering_enabled(self):
        return (self.ppumask & 0x18) != 0

    def _inc_scroll_x(self):
        if not self._rendering_enabled():
            return
        if (self.v & 0x001F) == 31:
            self.v &= ~0x001F
            self.v ^= 0x0400
        else:
            self.v += 1

    def _inc_scroll_y(self):
        if not self._rendering_enabled():
            return
        if (self.v & 0x7000) != 0x7000:
            self.v += 0x1000
        else:
            self.v &= ~0x7000
            y = (self.v & 0x03E0) >> 5
            if y == 29:
                y = 0
                self.v ^= 0x0800
            elif y == 31:
                y = 0
            else:
                y += 1
            self.v = (self.v & ~0x03E0) | (y << 5)

    def _copy_scroll_x(self):
        if self._rendering_enabled():
            self.v = (self.v & 0xFBE0) | (self.t & 0x041F)

    def _copy_scroll_y(self):
        if self._rendering_enabled():
            self.v = (self.v & 0x841F) | (self.t & 0x7BE0)

    def _load_bg_shifters(self):
        self._bg_shift_pat_lo = (self._bg_shift_pat_lo & 0xFF00) | self._bg_next_lo
        self._bg_shift_pat_hi = (self._bg_shift_pat_hi & 0xFF00) | self._bg_next_hi
        self._bg_shift_attr_lo = (self._bg_shift_attr_lo & 0xFF00) | (0xFF if (self._bg_next_attr & 1) else 0x00)
        self._bg_shift_attr_hi = (self._bg_shift_attr_hi & 0xFF00) | (0xFF if (self._bg_next_attr & 2) else 0x00)

    def _shift_bg_shifters(self):
        if self.ppumask & 0x08:
            self._bg_shift_pat_lo <<= 1
            self._bg_shift_pat_hi <<= 1
            self._bg_shift_attr_lo <<= 1
            self._bg_shift_attr_hi <<= 1

    def _fetch_bg_tile(self):
        """Fetch the next background tile data."""
        nt_addr = 0x2000 | (self.v & 0x0FFF)
        self._bg_next_tile_id = self.ppu_read(nt_addr)

        at_addr = 0x23C0 | (self.v & 0x0C00) | ((self.v >> 4) & 0x38) | ((self.v >> 2) & 0x07)
        at_byte = self.ppu_read(at_addr)
        if self.v & 0x40: at_byte >>= 4
        if self.v & 0x02: at_byte >>= 2
        self._bg_next_attr = at_byte & 0x03

        bg_pattern_base = 0x1000 if (self.ppuctrl & 0x10) else 0x0000
        fine_y = (self.v >> 12) & 0x07
        tile_addr = bg_pattern_base + self._bg_next_tile_id * 16 + fine_y
        self._bg_next_lo = self.ppu_read(tile_addr)
        self._bg_next_hi = self.ppu_read(tile_addr + 8)

    # ---- Sprite Evaluation ----
    def _evaluate_sprites(self):
        """Evaluate which sprites are on the current scanline."""
        sprite_height = 16 if (self.ppuctrl & 0x20) else 8
        self._sprite_count = 0
        self.sprite_zero_on_line = False

        for i in range(64):
            sy = self.oam[i * 4]
            diff = self.scanline - sy
            if 0 <= diff < sprite_height:
                if self._sprite_count < 8:
                    if i == 0:
                        self.sprite_zero_on_line = True
                    self._sprite_indices[self._sprite_count] = i

                    tile = self.oam[i * 4 + 1]
                    attr = self.oam[i * 4 + 2]
                    sx = self.oam[i * 4 + 3]
                    flip_v = bool(attr & 0x80)
                    flip_h = bool(attr & 0x40)

                    if sprite_height == 8:
                        spr_pat_base = 0x1000 if (self.ppuctrl & 0x08) else 0x0000
                        row = (7 - diff) if flip_v else diff
                        pat_addr = spr_pat_base + tile * 16 + row
                    else:
                        # 8x16 sprites
                        spr_pat_base = 0x1000 if (tile & 1) else 0x0000
                        tile &= 0xFE
                        if flip_v:
                            row = 15 - diff
                        else:
                            row = diff
                        if row >= 8:
                            tile += 1
                            row -= 8
                        pat_addr = spr_pat_base + tile * 16 + row

                    lo = self.ppu_read(pat_addr)
                    hi = self.ppu_read(pat_addr + 8)

                    if flip_h:
                        # Reverse bits
                        lo = int(f'{lo:08b}'[::-1], 2)
                        hi = int(f'{hi:08b}'[::-1], 2)

                    self._sprite_patterns_lo[self._sprite_count] = lo
                    self._sprite_patterns_hi[self._sprite_count] = hi
                    self._sprite_positions[self._sprite_count] = sx
                    self._sprite_priorities[self._sprite_count] = (attr >> 5) & 1

                    self._sprite_count += 1
                else:
                    self.ppustatus |= 0x20  # Sprite overflow
                    break

    # ---- Render one full scanline ----
    def render_scanline(self):
        """Render pixels for the current visible scanline (0-239)."""
        y = self.scanline
        if y >= 240:
            return

        rendering = self._rendering_enabled()
        if not rendering:
            bg_color_idx = self.palette_ram[0] & 0x3F
            base = y * 256
            for x in range(256):
                self.framebuffer[base + x] = bg_color_idx
            return

        # Evaluate sprites for this scanline
        self._evaluate_sprites()

        # Fetch first two background tiles
        self._fetch_bg_tile()
        self._load_bg_shifters()
        self._inc_scroll_x()
        self._fetch_bg_tile()

        base = y * 256

        for x in range(256):
            # --- Background pixel ---
            bg_pixel = 0
            bg_palette = 0
            if self.ppumask & 0x08:
                if (self.ppumask & 0x02) or x >= 8:
                    bit_sel = 0x8000 >> self.fine_x
                    p0 = 1 if (self._bg_shift_pat_lo & bit_sel) else 0
                    p1 = 1 if (self._bg_shift_pat_hi & bit_sel) else 0
                    bg_pixel = (p1 << 1) | p0
                    a0 = 1 if (self._bg_shift_attr_lo & bit_sel) else 0
                    a1 = 1 if (self._bg_shift_attr_hi & bit_sel) else 0
                    bg_palette = (a1 << 1) | a0

            # --- Sprite pixel ---
            spr_pixel = 0
            spr_palette = 0
            spr_priority = 0
            spr_is_zero = False

            if self.ppumask & 0x10:
                if (self.ppumask & 0x04) or x >= 8:
                    for s in range(self._sprite_count):
                        sx = self._sprite_positions[s]
                        offset = x - sx
                        if 0 <= offset < 8:
                            bit = 7 - offset
                            p0 = (self._sprite_patterns_lo[s] >> bit) & 1
                            p1 = (self._sprite_patterns_hi[s] >> bit) & 1
                            pixel = (p1 << 1) | p0
                            if pixel != 0:
                                spr_pixel = pixel
                                attr = self.oam[self._sprite_indices[s] * 4 + 2]
                                spr_palette = (attr & 0x03) + 4
                                spr_priority = self._sprite_priorities[s]
                                if self._sprite_indices[s] == 0:
                                    spr_is_zero = True
                                break

            # --- Priority multiplexer ---
            if bg_pixel == 0 and spr_pixel == 0:
                color_idx = self.palette_ram[0] & 0x3F
            elif bg_pixel == 0 and spr_pixel != 0:
                color_idx = self.ppu_read(0x3F00 + spr_palette * 4 + spr_pixel)
            elif bg_pixel != 0 and spr_pixel == 0:
                color_idx = self.ppu_read(0x3F00 + bg_palette * 4 + bg_pixel)
            else:
                # Sprite-0 hit detection
                if spr_is_zero and self.sprite_zero_on_line and x < 255:
                    if not self.sprite_zero_hit:
                        self.sprite_zero_hit = True
                        self.ppustatus |= 0x40

                if spr_priority == 0:
                    color_idx = self.ppu_read(0x3F00 + spr_palette * 4 + spr_pixel)
                else:
                    color_idx = self.ppu_read(0x3F00 + bg_palette * 4 + bg_pixel)

            self.framebuffer[base + x] = color_idx & 0x3F

            # Shift background registers
            self._shift_bg_shifters()

            # Every 8 pixels, load new tile
            if (x + 1) % 8 == 0 and x < 255:
                self._load_bg_shifters()
                self._inc_scroll_x()
                self._fetch_bg_tile()

        # End of visible scanline: increment Y scroll
        self._inc_scroll_y()

    # ---- Tick: advance one full scanline ----
    def tick_scanline(self):
        """Advance the PPU by one scanline. Returns True if NMI should fire."""
        nmi_trigger = False

        if self.scanline < 240:
            # Visible scanline
            if self.scanline == 0:
                # Copy horizontal scroll at start of frame
                pass
            self.render_scanline()
            if self._rendering_enabled():
                self._copy_scroll_x()

        elif self.scanline == 241:
            # Enter VBLANK
            self.ppustatus |= 0x80
            self.nmi_occurred = True
            if self.nmi_output:
                nmi_trigger = True

        elif self.scanline == 261:
            # Pre-render scanline
            self.ppustatus &= ~0xE0
            self.nmi_occurred = False
            self.sprite_zero_hit = False
            if self._rendering_enabled():
                self._copy_scroll_y()
                self._copy_scroll_x()

        self.scanline += 1
        if self.scanline > 261:
            self.scanline = 0
            self.frame_count += 1
            self.odd_frame = not self.odd_frame

        return nmi_trigger


# ============================================================
# CPU - 6502 Processor (Full Official Instruction Set)
# ============================================================
class CPU6502:
    def __init__(self, ppu: PPU):
        self.ppu = ppu
        self.ram = bytearray(0x0800)
        self.prg_rom = bytearray(0x8000)
        self.prg_size = 0

        # Registers
        self.pc = 0
        self.a = 0
        self.x = 0
        self.y = 0
        self.sp = 0xFD
        self.status = 0x24

        # Controller state: button bits (A,B,Sel,Start,Up,Dn,L,R)
        self.controller_state = [0, 0]  # Player 1 & 2
        self.controller_shift = [0, 0]
        self.controller_strobe = 0

        # Cycle counter
        self.cycles = 0
        self.stall = 0

        # Build opcode table
        self._build_optable()

    # ---- Status flag helpers ----
    FLAG_C = 0x01
    FLAG_Z = 0x02
    FLAG_I = 0x04
    FLAG_D = 0x08
    FLAG_B = 0x10
    FLAG_U = 0x20
    FLAG_V = 0x40
    FLAG_N = 0x80

    def _set_flag(self, flag, val):
        if val:
            self.status |= flag
        else:
            self.status &= ~flag

    def _get_flag(self, flag):
        return 1 if (self.status & flag) else 0

    def _set_zn(self, val):
        self._set_flag(self.FLAG_Z, val == 0)
        self._set_flag(self.FLAG_N, val & 0x80)

    # ---- Memory access ----
    def read(self, addr):
        addr &= 0xFFFF
        if addr < 0x2000:
            return self.ram[addr & 0x07FF]
        elif addr < 0x4000:
            return self.ppu.cpu_read(addr & 7)
        elif addr == 0x4016:
            val = self.controller_shift[0] & 1
            self.controller_shift[0] >>= 1
            return val | 0x40
        elif addr == 0x4017:
            val = self.controller_shift[1] & 1
            self.controller_shift[1] >>= 1
            return val | 0x40
        elif addr < 0x4020:
            return 0  # APU/IO
        elif addr >= 0x8000:
            offset = addr - 0x8000
            if self.prg_size <= 0x4000:
                return self.prg_rom[offset & 0x3FFF]
            return self.prg_rom[offset & 0x7FFF]
        return 0

    def write(self, addr, val):
        addr &= 0xFFFF
        val &= 0xFF
        if addr < 0x2000:
            self.ram[addr & 0x07FF] = val
        elif addr < 0x4000:
            self.ppu.cpu_write(addr & 7, val)
        elif addr == 0x4014:
            # OAM DMA
            page = val << 8
            for i in range(256):
                self.ppu.oam[(self.ppu.oamaddr + i) & 0xFF] = self.read(page + i)
            self.stall += 513
        elif addr == 0x4016:
            self.controller_strobe = val & 1
            if self.controller_strobe:
                self.controller_shift[0] = self.controller_state[0]
                self.controller_shift[1] = self.controller_state[1]
        elif addr < 0x4020:
            pass  # APU stubs

    def read16(self, addr):
        lo = self.read(addr)
        hi = self.read((addr + 1) & 0xFFFF)
        return (hi << 8) | lo

    def read16_bug(self, addr):
        """Read 16-bit with 6502 page boundary bug (JMP indirect)."""
        lo = self.read(addr)
        hi_addr = (addr & 0xFF00) | ((addr + 1) & 0xFF)
        hi = self.read(hi_addr)
        return (hi << 8) | lo

    def push(self, val):
        self.write(0x0100 | self.sp, val & 0xFF)
        self.sp = (self.sp - 1) & 0xFF

    def pull(self):
        self.sp = (self.sp + 1) & 0xFF
        return self.read(0x0100 | self.sp)

    def push16(self, val):
        self.push((val >> 8) & 0xFF)
        self.push(val & 0xFF)

    def pull16(self):
        lo = self.pull()
        hi = self.pull()
        return (hi << 8) | lo

    # ---- Addressing Modes ----
    def _addr_imp(self): return 0
    def _addr_acc(self): return 0
    def _addr_imm(self):
        a = self.pc; self.pc = (self.pc + 1) & 0xFFFF; return a
    def _addr_zp(self):
        a = self.read(self.pc) & 0xFF; self.pc = (self.pc + 1) & 0xFFFF; return a
    def _addr_zpx(self):
        a = (self.read(self.pc) + self.x) & 0xFF; self.pc = (self.pc + 1) & 0xFFFF; return a
    def _addr_zpy(self):
        a = (self.read(self.pc) + self.y) & 0xFF; self.pc = (self.pc + 1) & 0xFFFF; return a
    def _addr_abs(self):
        a = self.read16(self.pc); self.pc = (self.pc + 2) & 0xFFFF; return a
    def _addr_abx(self):
        a = (self.read16(self.pc) + self.x) & 0xFFFF; self.pc = (self.pc + 2) & 0xFFFF; return a
    def _addr_aby(self):
        a = (self.read16(self.pc) + self.y) & 0xFFFF; self.pc = (self.pc + 2) & 0xFFFF; return a
    def _addr_ind(self):
        a = self.read16(self.pc); self.pc = (self.pc + 2) & 0xFFFF; return self.read16_bug(a)
    def _addr_izx(self):
        ptr = (self.read(self.pc) + self.x) & 0xFF; self.pc = (self.pc + 1) & 0xFFFF
        lo = self.read(ptr); hi = self.read((ptr + 1) & 0xFF); return (hi << 8) | lo
    def _addr_izy(self):
        ptr = self.read(self.pc); self.pc = (self.pc + 1) & 0xFFFF
        lo = self.read(ptr); hi = self.read((ptr + 1) & 0xFF)
        return ((hi << 8) | lo + self.y) & 0xFFFF
    def _addr_rel(self):
        off = self.read(self.pc); self.pc = (self.pc + 1) & 0xFFFF
        if off & 0x80: off -= 256
        return (self.pc + off) & 0xFFFF

    # ---- Instructions ----
    def _adc(self, addr):
        val = self.read(addr)
        c = self._get_flag(self.FLAG_C)
        s = self.a + val + c
        self._set_flag(self.FLAG_C, s > 0xFF)
        self._set_flag(self.FLAG_V, (~(self.a ^ val) & (self.a ^ s)) & 0x80)
        self.a = s & 0xFF
        self._set_zn(self.a)

    def _and(self, addr):
        self.a &= self.read(addr); self._set_zn(self.a)

    def _asl_acc(self, _):
        self._set_flag(self.FLAG_C, self.a & 0x80)
        self.a = (self.a << 1) & 0xFF; self._set_zn(self.a)

    def _asl_mem(self, addr):
        val = self.read(addr)
        self._set_flag(self.FLAG_C, val & 0x80)
        val = (val << 1) & 0xFF; self.write(addr, val); self._set_zn(val)

    def _branch(self, addr, cond):
        if cond: self.pc = addr; self.cycles += 1

    def _bcc(self, addr): self._branch(addr, not self._get_flag(self.FLAG_C))
    def _bcs(self, addr): self._branch(addr, self._get_flag(self.FLAG_C))
    def _beq(self, addr): self._branch(addr, self._get_flag(self.FLAG_Z))
    def _bmi(self, addr): self._branch(addr, self._get_flag(self.FLAG_N))
    def _bne(self, addr): self._branch(addr, not self._get_flag(self.FLAG_Z))
    def _bpl(self, addr): self._branch(addr, not self._get_flag(self.FLAG_N))
    def _bvc(self, addr): self._branch(addr, not self._get_flag(self.FLAG_V))
    def _bvs(self, addr): self._branch(addr, self._get_flag(self.FLAG_V))

    def _bit(self, addr):
        val = self.read(addr)
        self._set_flag(self.FLAG_Z, (self.a & val) == 0)
        self._set_flag(self.FLAG_V, val & 0x40)
        self._set_flag(self.FLAG_N, val & 0x80)

    def _brk(self, _):
        self.pc = (self.pc + 1) & 0xFFFF
        self.push16(self.pc)
        self.push(self.status | 0x30)
        self._set_flag(self.FLAG_I, True)
        self.pc = self.read16(0xFFFE)

    def _clc(self, _): self._set_flag(self.FLAG_C, False)
    def _cld(self, _): self._set_flag(self.FLAG_D, False)
    def _cli(self, _): self._set_flag(self.FLAG_I, False)
    def _clv(self, _): self._set_flag(self.FLAG_V, False)

    def _cmp(self, addr):
        val = self.read(addr); r = self.a - val
        self._set_flag(self.FLAG_C, self.a >= val); self._set_zn(r & 0xFF)

    def _cpx(self, addr):
        val = self.read(addr); r = self.x - val
        self._set_flag(self.FLAG_C, self.x >= val); self._set_zn(r & 0xFF)

    def _cpy(self, addr):
        val = self.read(addr); r = self.y - val
        self._set_flag(self.FLAG_C, self.y >= val); self._set_zn(r & 0xFF)

    def _dec(self, addr):
        val = (self.read(addr) - 1) & 0xFF; self.write(addr, val); self._set_zn(val)

    def _dex(self, _): self.x = (self.x - 1) & 0xFF; self._set_zn(self.x)
    def _dey(self, _): self.y = (self.y - 1) & 0xFF; self._set_zn(self.y)

    def _eor(self, addr):
        self.a ^= self.read(addr); self._set_zn(self.a)

    def _inc(self, addr):
        val = (self.read(addr) + 1) & 0xFF; self.write(addr, val); self._set_zn(val)

    def _inx(self, _): self.x = (self.x + 1) & 0xFF; self._set_zn(self.x)
    def _iny(self, _): self.y = (self.y + 1) & 0xFF; self._set_zn(self.y)

    def _jmp(self, addr): self.pc = addr
    def _jsr(self, addr): self.push16((self.pc - 1) & 0xFFFF); self.pc = addr

    def _lda(self, addr): self.a = self.read(addr); self._set_zn(self.a)
    def _ldx(self, addr): self.x = self.read(addr); self._set_zn(self.x)
    def _ldy(self, addr): self.y = self.read(addr); self._set_zn(self.y)

    def _lsr_acc(self, _):
        self._set_flag(self.FLAG_C, self.a & 1)
        self.a >>= 1; self._set_zn(self.a)

    def _lsr_mem(self, addr):
        val = self.read(addr)
        self._set_flag(self.FLAG_C, val & 1)
        val >>= 1; self.write(addr, val); self._set_zn(val)

    def _nop(self, _): pass

    def _ora(self, addr):
        self.a |= self.read(addr); self._set_zn(self.a)

    def _pha(self, _): self.push(self.a)
    def _php(self, _): self.push(self.status | 0x30)
    def _pla(self, _): self.a = self.pull(); self._set_zn(self.a)
    def _plp(self, _): self.status = (self.pull() & 0xEF) | 0x20

    def _rol_acc(self, _):
        c = self._get_flag(self.FLAG_C)
        self._set_flag(self.FLAG_C, self.a & 0x80)
        self.a = ((self.a << 1) | c) & 0xFF; self._set_zn(self.a)

    def _rol_mem(self, addr):
        val = self.read(addr); c = self._get_flag(self.FLAG_C)
        self._set_flag(self.FLAG_C, val & 0x80)
        val = ((val << 1) | c) & 0xFF; self.write(addr, val); self._set_zn(val)

    def _ror_acc(self, _):
        c = self._get_flag(self.FLAG_C)
        self._set_flag(self.FLAG_C, self.a & 1)
        self.a = (self.a >> 1) | (c << 7); self._set_zn(self.a)

    def _ror_mem(self, addr):
        val = self.read(addr); c = self._get_flag(self.FLAG_C)
        self._set_flag(self.FLAG_C, val & 1)
        val = (val >> 1) | (c << 7); self.write(addr, val); self._set_zn(val)

    def _rti(self, _):
        self.status = (self.pull() & 0xEF) | 0x20
        self.pc = self.pull16()

    def _rts(self, _):
        self.pc = (self.pull16() + 1) & 0xFFFF

    def _sbc(self, addr):
        val = self.read(addr)
        c = self._get_flag(self.FLAG_C)
        s = self.a - val - (1 - c)
        self._set_flag(self.FLAG_C, s >= 0)
        self._set_flag(self.FLAG_V, ((self.a ^ val) & (self.a ^ s)) & 0x80)
        self.a = s & 0xFF; self._set_zn(self.a)

    def _sec(self, _): self._set_flag(self.FLAG_C, True)
    def _sed(self, _): self._set_flag(self.FLAG_D, True)
    def _sei(self, _): self._set_flag(self.FLAG_I, True)

    def _sta(self, addr): self.write(addr, self.a)
    def _stx(self, addr): self.write(addr, self.x)
    def _sty(self, addr): self.write(addr, self.y)

    def _tax(self, _): self.x = self.a; self._set_zn(self.x)
    def _tay(self, _): self.y = self.a; self._set_zn(self.y)
    def _tsx(self, _): self.x = self.sp; self._set_zn(self.x)
    def _txa(self, _): self.a = self.x; self._set_zn(self.a)
    def _txs(self, _): self.sp = self.x
    def _tya(self, _): self.a = self.y; self._set_zn(self.a)

    def _nop_read(self, addr):
        """Unofficial NOP that reads (used by some games)."""
        self.read(addr)

    # ---- Unofficial but common opcodes ----
    def _lax(self, addr):
        self.a = self.x = self.read(addr); self._set_zn(self.a)
    def _sax(self, addr):
        self.write(addr, self.a & self.x)
    def _dcp(self, addr):
        val = (self.read(addr) - 1) & 0xFF; self.write(addr, val)
        r = self.a - val; self._set_flag(self.FLAG_C, self.a >= val); self._set_zn(r & 0xFF)
    def _isb(self, addr):
        val = (self.read(addr) + 1) & 0xFF; self.write(addr, val)
        self._sbc_val(val)
    def _sbc_val(self, val):
        c = self._get_flag(self.FLAG_C)
        s = self.a - val - (1 - c)
        self._set_flag(self.FLAG_C, s >= 0)
        self._set_flag(self.FLAG_V, ((self.a ^ val) & (self.a ^ s)) & 0x80)
        self.a = s & 0xFF; self._set_zn(self.a)
    def _slo(self, addr):
        val = self.read(addr); self._set_flag(self.FLAG_C, val & 0x80)
        val = (val << 1) & 0xFF; self.write(addr, val)
        self.a |= val; self._set_zn(self.a)
    def _rla(self, addr):
        val = self.read(addr); c = self._get_flag(self.FLAG_C)
        self._set_flag(self.FLAG_C, val & 0x80)
        val = ((val << 1) | c) & 0xFF; self.write(addr, val)
        self.a &= val; self._set_zn(self.a)
    def _sre(self, addr):
        val = self.read(addr); self._set_flag(self.FLAG_C, val & 1)
        val >>= 1; self.write(addr, val)
        self.a ^= val; self._set_zn(self.a)
    def _rra(self, addr):
        val = self.read(addr); c = self._get_flag(self.FLAG_C)
        self._set_flag(self.FLAG_C, val & 1)
        val = (val >> 1) | (c << 7); self.write(addr, val)
        # Now ADC
        c2 = self._get_flag(self.FLAG_C)
        s = self.a + val + c2
        self._set_flag(self.FLAG_C, s > 0xFF)
        self._set_flag(self.FLAG_V, (~(self.a ^ val) & (self.a ^ s)) & 0x80)
        self.a = s & 0xFF; self._set_zn(self.a)

    # ---- Opcode table builder ----
    def _build_optable(self):
        """Build full 256-entry opcode dispatch table.
        Each entry: (handler, addr_mode, cycles)
        """
        nop = (self._nop, self._addr_imp, 2)
        self.optable = [nop] * 256

        def op(code, handler, mode, cyc):
            self.optable[code] = (handler, mode, cyc)

        I, A, Z, ZX, ZY = self._addr_imp, self._addr_acc, self._addr_zp, self._addr_zpx, self._addr_zpy
        AB, AX, AY = self._addr_abs, self._addr_abx, self._addr_aby
        IX, IY, ID = self._addr_izx, self._addr_izy, self._addr_ind
        IM, R = self._addr_imm, self._addr_rel

        # ADC
        op(0x69, self._adc, IM, 2); op(0x65, self._adc, Z, 3); op(0x75, self._adc, ZX, 4)
        op(0x6D, self._adc, AB, 4); op(0x7D, self._adc, AX, 4); op(0x79, self._adc, AY, 4)
        op(0x61, self._adc, IX, 6); op(0x71, self._adc, IY, 5)
        # AND
        op(0x29, self._and, IM, 2); op(0x25, self._and, Z, 3); op(0x35, self._and, ZX, 4)
        op(0x2D, self._and, AB, 4); op(0x3D, self._and, AX, 4); op(0x39, self._and, AY, 4)
        op(0x21, self._and, IX, 6); op(0x31, self._and, IY, 5)
        # ASL
        op(0x0A, self._asl_acc, A, 2); op(0x06, self._asl_mem, Z, 5); op(0x16, self._asl_mem, ZX, 6)
        op(0x0E, self._asl_mem, AB, 6); op(0x1E, self._asl_mem, AX, 7)
        # Branches
        op(0x90, self._bcc, R, 2); op(0xB0, self._bcs, R, 2)
        op(0xF0, self._beq, R, 2); op(0x30, self._bmi, R, 2)
        op(0xD0, self._bne, R, 2); op(0x10, self._bpl, R, 2)
        op(0x50, self._bvc, R, 2); op(0x70, self._bvs, R, 2)
        # BIT
        op(0x24, self._bit, Z, 3); op(0x2C, self._bit, AB, 4)
        # BRK
        op(0x00, self._brk, I, 7)
        # Clear/Set flags
        op(0x18, self._clc, I, 2); op(0xD8, self._cld, I, 2)
        op(0x58, self._cli, I, 2); op(0xB8, self._clv, I, 2)
        op(0x38, self._sec, I, 2); op(0xF8, self._sed, I, 2); op(0x78, self._sei, I, 2)
        # CMP
        op(0xC9, self._cmp, IM, 2); op(0xC5, self._cmp, Z, 3); op(0xD5, self._cmp, ZX, 4)
        op(0xCD, self._cmp, AB, 4); op(0xDD, self._cmp, AX, 4); op(0xD9, self._cmp, AY, 4)
        op(0xC1, self._cmp, IX, 6); op(0xD1, self._cmp, IY, 5)
        # CPX
        op(0xE0, self._cpx, IM, 2); op(0xE4, self._cpx, Z, 3); op(0xEC, self._cpx, AB, 4)
        # CPY
        op(0xC0, self._cpy, IM, 2); op(0xC4, self._cpy, Z, 3); op(0xCC, self._cpy, AB, 4)
        # DEC
        op(0xC6, self._dec, Z, 5); op(0xD6, self._dec, ZX, 6)
        op(0xCE, self._dec, AB, 6); op(0xDE, self._dec, AX, 7)
        # DEX/DEY
        op(0xCA, self._dex, I, 2); op(0x88, self._dey, I, 2)
        # EOR
        op(0x49, self._eor, IM, 2); op(0x45, self._eor, Z, 3); op(0x55, self._eor, ZX, 4)
        op(0x4D, self._eor, AB, 4); op(0x5D, self._eor, AX, 4); op(0x59, self._eor, AY, 4)
        op(0x41, self._eor, IX, 6); op(0x51, self._eor, IY, 5)
        # INC
        op(0xE6, self._inc, Z, 5); op(0xF6, self._inc, ZX, 6)
        op(0xEE, self._inc, AB, 6); op(0xFE, self._inc, AX, 7)
        # INX/INY
        op(0xE8, self._inx, I, 2); op(0xC8, self._iny, I, 2)
        # JMP
        op(0x4C, self._jmp, AB, 3); op(0x6C, self._jmp, ID, 5)
        # JSR
        op(0x20, self._jsr, AB, 6)
        # LDA
        op(0xA9, self._lda, IM, 2); op(0xA5, self._lda, Z, 3); op(0xB5, self._lda, ZX, 4)
        op(0xAD, self._lda, AB, 4); op(0xBD, self._lda, AX, 4); op(0xB9, self._lda, AY, 4)
        op(0xA1, self._lda, IX, 6); op(0xB1, self._lda, IY, 5)
        # LDX
        op(0xA2, self._ldx, IM, 2); op(0xA6, self._ldx, Z, 3); op(0xB6, self._ldx, ZY, 4)
        op(0xAE, self._ldx, AB, 4); op(0xBE, self._ldx, AY, 4)
        # LDY
        op(0xA0, self._ldy, IM, 2); op(0xA4, self._ldy, Z, 3); op(0xB4, self._ldy, ZX, 4)
        op(0xAC, self._ldy, AB, 4); op(0xBC, self._ldy, AX, 4)
        # LSR
        op(0x4A, self._lsr_acc, A, 2); op(0x46, self._lsr_mem, Z, 5); op(0x56, self._lsr_mem, ZX, 6)
        op(0x4E, self._lsr_mem, AB, 6); op(0x5E, self._lsr_mem, AX, 7)
        # NOP
        op(0xEA, self._nop, I, 2)
        # ORA
        op(0x09, self._ora, IM, 2); op(0x05, self._ora, Z, 3); op(0x15, self._ora, ZX, 4)
        op(0x0D, self._ora, AB, 4); op(0x1D, self._ora, AX, 4); op(0x19, self._ora, AY, 4)
        op(0x01, self._ora, IX, 6); op(0x11, self._ora, IY, 5)
        # Stack
        op(0x48, self._pha, I, 3); op(0x08, self._php, I, 3)
        op(0x68, self._pla, I, 4); op(0x28, self._plp, I, 4)
        # ROL
        op(0x2A, self._rol_acc, A, 2); op(0x26, self._rol_mem, Z, 5); op(0x36, self._rol_mem, ZX, 6)
        op(0x2E, self._rol_mem, AB, 6); op(0x3E, self._rol_mem, AX, 7)
        # ROR
        op(0x6A, self._ror_acc, A, 2); op(0x66, self._ror_mem, Z, 5); op(0x76, self._ror_mem, ZX, 6)
        op(0x6E, self._ror_mem, AB, 6); op(0x7E, self._ror_mem, AX, 7)
        # RTI / RTS
        op(0x40, self._rti, I, 6); op(0x60, self._rts, I, 6)
        # SBC
        op(0xE9, self._sbc, IM, 2); op(0xE5, self._sbc, Z, 3); op(0xF5, self._sbc, ZX, 4)
        op(0xED, self._sbc, AB, 4); op(0xFD, self._sbc, AX, 4); op(0xF9, self._sbc, AY, 4)
        op(0xE1, self._sbc, IX, 6); op(0xF1, self._sbc, IY, 5)
        op(0xEB, self._sbc, IM, 2)  # Unofficial mirror
        # STA
        op(0x85, self._sta, Z, 3); op(0x95, self._sta, ZX, 4)
        op(0x8D, self._sta, AB, 4); op(0x9D, self._sta, AX, 5); op(0x99, self._sta, AY, 5)
        op(0x81, self._sta, IX, 6); op(0x91, self._sta, IY, 6)
        # STX
        op(0x86, self._stx, Z, 3); op(0x96, self._stx, ZY, 4); op(0x8E, self._stx, AB, 4)
        # STY
        op(0x84, self._sty, Z, 3); op(0x94, self._sty, ZX, 4); op(0x8C, self._sty, AB, 4)
        # Transfers
        op(0xAA, self._tax, I, 2); op(0xA8, self._tay, I, 2)
        op(0xBA, self._tsx, I, 2); op(0x8A, self._txa, I, 2)
        op(0x9A, self._txs, I, 2); op(0x98, self._tya, I, 2)

        # Common unofficial NOPs (many games use these)
        for opc in [0x1A,0x3A,0x5A,0x7A,0xDA,0xFA]:
            op(opc, self._nop, I, 2)
        for opc in [0x04,0x44,0x64]:
            op(opc, self._nop_read, Z, 3)
        for opc in [0x0C]:
            op(opc, self._nop_read, AB, 4)
        for opc in [0x14,0x34,0x54,0x74,0xD4,0xF4]:
            op(opc, self._nop_read, ZX, 4)
        for opc in [0x1C,0x3C,0x5C,0x7C,0xDC,0xFC]:
            op(opc, self._nop_read, AX, 4)
        op(0x80, self._nop_read, IM, 2)
        op(0x82, self._nop_read, IM, 2)
        op(0x89, self._nop_read, IM, 2)
        op(0xC2, self._nop_read, IM, 2)
        op(0xE2, self._nop_read, IM, 2)

        # Unofficial combos (needed by many commercial games)
        op(0xA7, self._lax, Z, 3); op(0xB7, self._lax, ZY, 4)
        op(0xAF, self._lax, AB, 4); op(0xBF, self._lax, AY, 4)
        op(0xA3, self._lax, IX, 6); op(0xB3, self._lax, IY, 5)
        op(0x87, self._sax, Z, 3); op(0x97, self._sax, ZY, 4)
        op(0x8F, self._sax, AB, 4); op(0x83, self._sax, IX, 6)
        op(0xC7, self._dcp, Z, 5); op(0xD7, self._dcp, ZX, 6)
        op(0xCF, self._dcp, AB, 6); op(0xDF, self._dcp, AX, 7)
        op(0xDB, self._dcp, AY, 7); op(0xC3, self._dcp, IX, 8); op(0xD3, self._dcp, IY, 8)
        op(0xE7, self._isb, Z, 5); op(0xF7, self._isb, ZX, 6)
        op(0xEF, self._isb, AB, 6); op(0xFF, self._isb, AX, 7)
        op(0xFB, self._isb, AY, 7); op(0xE3, self._isb, IX, 8); op(0xF3, self._isb, IY, 8)
        op(0x07, self._slo, Z, 5); op(0x17, self._slo, ZX, 6)
        op(0x0F, self._slo, AB, 6); op(0x1F, self._slo, AX, 7)
        op(0x1B, self._slo, AY, 7); op(0x03, self._slo, IX, 8); op(0x13, self._slo, IY, 8)
        op(0x27, self._rla, Z, 5); op(0x37, self._rla, ZX, 6)
        op(0x2F, self._rla, AB, 6); op(0x3F, self._rla, AX, 7)
        op(0x3B, self._rla, AY, 7); op(0x23, self._rla, IX, 8); op(0x33, self._rla, IY, 8)
        op(0x47, self._sre, Z, 5); op(0x57, self._sre, ZX, 6)
        op(0x4F, self._sre, AB, 6); op(0x5F, self._sre, AX, 7)
        op(0x5B, self._sre, AY, 7); op(0x43, self._sre, IX, 8); op(0x53, self._sre, IY, 8)
        op(0x67, self._rra, Z, 5); op(0x77, self._rra, ZX, 6)
        op(0x6F, self._rra, AB, 6); op(0x7F, self._rra, AX, 7)
        op(0x7B, self._rra, AY, 7); op(0x63, self._rra, IX, 8); op(0x73, self._rra, IY, 8)

    # ---- Execute one instruction ----
    def step(self):
        if self.stall > 0:
            self.stall -= 1
            self.cycles += 1
            return

        opcode = self.read(self.pc)
        self.pc = (self.pc + 1) & 0xFFFF
        handler, mode, cyc = self.optable[opcode]
        addr = mode()
        handler(addr)
        self.cycles += cyc

    # ---- Reset ----
    def reset(self):
        self.pc = self.read16(0xFFFC)
        if self.pc == 0:
            self.pc = 0x8000
        self.sp = 0xFD
        self.status = 0x24
        self.a = self.x = self.y = 0
        self.cycles = 0
        self.stall = 0

    def nmi(self):
        self.push16(self.pc)
        self.push((self.status | 0x20) & ~0x10)
        self._set_flag(self.FLAG_I, True)
        self.pc = self.read16(0xFFFA)
        self.cycles += 7

    def irq(self):
        if not self._get_flag(self.FLAG_I):
            self.push16(self.pc)
            self.push((self.status | 0x20) & ~0x10)
            self._set_flag(self.FLAG_I, True)
            self.pc = self.read16(0xFFFE)
            self.cycles += 7

    def load_prg(self, data):
        self.prg_size = len(data)
        if self.prg_size <= 0x8000:
            self.prg_rom[:self.prg_size] = data
            if self.prg_size == 0x4000:
                self.prg_rom[0x4000:0x8000] = data


# ============================================================
# GUI / Main Application
# ============================================================
class ACHoldingsNesEmu:
    SCALE = 2
    WIDTH = 256
    HEIGHT = 240

    # Key mappings → NES controller bits
    # A, B, Select, Start, Up, Down, Left, Right
    KEY_MAP = {
        'z': 0, 'x': 1, 'BackSpace': 2, 'Return': 3,
        'Up': 4, 'Down': 5, 'Left': 6, 'Right': 7,
    }

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("AC HOLDINGS NES EMU 2.0 - FULL PPU CORE")
        win_w = self.WIDTH * self.SCALE + 240
        win_h = self.HEIGHT * self.SCALE + 40
        self.root.geometry(f"{win_w}x{win_h}")
        self.root.configure(bg="#0a0a0a")
        self.root.resizable(False, False)

        self.ppu = PPU()
        self.cpu = CPU6502(self.ppu)
        self.is_running = False
        self.rom_loaded = False
        self.frame_count = 0
        self.fps = 0.0
        self.last_time = time.time()

        self._build_gui()
        self._bind_keys()

    def _build_gui(self):
        # Menu
        menubar = tk.Menu(self.root)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open ROM...", command=self.open_rom)
        file_menu.add_separator()
        file_menu.add_command(label="Reset", command=self.reset_system)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)
        menubar.add_cascade(label="File", menu=file_menu)
        self.root.config(menu=menubar)

        # Display canvas
        disp_w = self.WIDTH * self.SCALE
        disp_h = self.HEIGHT * self.SCALE
        self.canvas = tk.Canvas(self.root, width=disp_w, height=disp_h, bg="black",
                                highlightthickness=1, highlightbackground="#333")
        self.canvas.place(x=10, y=10)

        # PhotoImage for rendering (1:1, then zoom)
        self.img = tk.PhotoImage(width=self.WIDTH, height=self.HEIGHT)
        self.img_id = self.canvas.create_image(0, 0, image=self.img, anchor=tk.NW)

        # Status panel
        panel_x = disp_w + 20
        panel_w = 220

        tk.Label(self.root, text="AC HOLDINGS NES EMU 2.0",
                 fg="#00FFFF", bg="#0a0a0a", font=("Courier", 11, "bold")).place(x=panel_x, y=10)
        tk.Label(self.root, text="FULL PPU NATIVE CORE",
                 fg="#666", bg="#0a0a0a", font=("Courier", 8)).place(x=panel_x, y=30)

        self.lbl_rom = tk.Label(self.root, text="ROM: ---", fg="white", bg="#0a0a0a", font=("Courier", 8))
        self.lbl_rom.place(x=panel_x, y=55)

        tk.Label(self.root, text="CPU REGISTERS", fg="#FFA500", bg="#0a0a0a",
                 font=("Courier", 9, "bold")).place(x=panel_x, y=80)
        self.lbl_regs = tk.Label(self.root, text="PC:---- A:-- X:-- Y:-- SP:--",
                                 fg="#00FF00", bg="#0a0a0a", font=("Courier", 9))
        self.lbl_regs.place(x=panel_x, y=100)
        self.lbl_status = tk.Label(self.root, text="NV-BDIZC: --------",
                                   fg="#00FF00", bg="#0a0a0a", font=("Courier", 9))
        self.lbl_status.place(x=panel_x, y=118)

        tk.Label(self.root, text="PPU STATE", fg="#FFA500", bg="#0a0a0a",
                 font=("Courier", 9, "bold")).place(x=panel_x, y=145)
        self.lbl_ppu = tk.Label(self.root, text="SL:--- CYC:--- FRM:---",
                                fg="#00FF00", bg="#0a0a0a", font=("Courier", 9))
        self.lbl_ppu.place(x=panel_x, y=165)
        self.lbl_scroll = tk.Label(self.root, text="V:---- T:---- FX:- W:-",
                                   fg="#00FF00", bg="#0a0a0a", font=("Courier", 9))
        self.lbl_scroll.place(x=panel_x, y=183)

        self.lbl_fps = tk.Label(self.root, text="FPS: --",
                                fg="#FFFF00", bg="#0a0a0a", font=("Courier", 9))
        self.lbl_fps.place(x=panel_x, y=210)

        tk.Label(self.root, text="CONTROLS", fg="#FFA500", bg="#0a0a0a",
                 font=("Courier", 9, "bold")).place(x=panel_x, y=240)
        ctrl_text = "Z=A  X=B  Enter=Start\nBksp=Select  Arrows=Pad"
        tk.Label(self.root, text=ctrl_text, fg="#888", bg="#0a0a0a",
                 font=("Courier", 8), justify=tk.LEFT).place(x=panel_x, y=260)

        # Buttons
        btn_y = disp_h - 20
        self.btn_run = tk.Button(self.root, text="RUN", bg="#1a3a1a", fg="#00FF00",
                                 font=("Courier", 9, "bold"), command=self.toggle_run,
                                 state=tk.DISABLED, width=8)
        self.btn_run.place(x=panel_x, y=btn_y)

        self.btn_step = tk.Button(self.root, text="STEP", bg="#1a1a3a", fg="#8888FF",
                                  font=("Courier", 9, "bold"), command=self.step_frame,
                                  state=tk.DISABLED, width=8)
        self.btn_step.place(x=panel_x + 90, y=btn_y)

        # Footer
        tk.Label(self.root, text="(C) 1999-2026 A.C Holdings / Team Flames",
                 fg="#333", bg="#0a0a0a", font=("Courier", 7)).place(x=10, y=disp_h + 18)

    def _bind_keys(self):
        self.root.bind("<KeyPress>", self._key_down)
        self.root.bind("<KeyRelease>", self._key_up)

    def _key_down(self, event):
        bit = self.KEY_MAP.get(event.keysym)
        if bit is not None:
            self.cpu.controller_state[0] |= (1 << bit)

    def _key_up(self, event):
        bit = self.KEY_MAP.get(event.keysym)
        if bit is not None:
            self.cpu.controller_state[0] &= ~(1 << bit)

    # ---- ROM Loading ----
    def open_rom(self):
        path = filedialog.askopenfilename(filetypes=[("NES ROM", "*.nes"), ("All", "*.*")])
        if not path:
            return
        try:
            with open(path, "rb") as f:
                header = f.read(16)
                if header[:4] != b"NES\x1a":
                    messagebox.showerror("Error", "Not a valid iNES ROM.")
                    return

                prg_banks = header[4]
                chr_banks = header[5]
                flags6 = header[6]
                flags7 = header[7]

                mirroring = 1 if (flags6 & 1) else 0
                has_trainer = bool(flags6 & 0x04)
                mapper = (flags6 >> 4) | (flags7 & 0xF0)

                if has_trainer:
                    f.read(512)

                prg_data = f.read(prg_banks * 16384)
                chr_data = f.read(chr_banks * 8192)

            if mapper != 0:
                messagebox.showwarning("Warning",
                    f"Mapper {mapper} detected. Only Mapper 0 (NROM) is supported.\n"
                    "Game may not work correctly.")

            # Load into system
            self.ppu.mirroring = mirroring
            self.cpu.load_prg(prg_data)

            if chr_banks > 0:
                self.ppu.chr_rom[:len(chr_data)] = chr_data
                self.ppu.chr_ram_mode = False
            else:
                self.ppu.chr_ram_mode = True

            self.reset_system()
            self.rom_loaded = True
            self.btn_run.config(state=tk.NORMAL)
            self.btn_step.config(state=tk.NORMAL)

            fname = os.path.basename(path)
            self.lbl_rom.config(text=f"ROM: {fname[:20]}")

        except Exception as e:
            messagebox.showerror("Load Error", str(e))

    def reset_system(self):
        self.is_running = False
        self.btn_run.config(text="RUN")
        self.ppu.scanline = 0
        self.ppu.ppustatus = 0
        self.ppu.ppuctrl = 0
        self.ppu.ppumask = 0
        self.ppu.v = 0
        self.ppu.t = 0
        self.ppu.fine_x = 0
        self.ppu.w = 0
        self.ppu.nmi_occurred = False
        self.ppu.sprite_zero_hit = False
        self.ppu.frame_count = 0
        self.cpu.reset()
        self.frame_count = 0
        self.update_status()

    # ---- Emulation Loop ----
    def run_one_frame(self):
        """Run CPU/PPU for exactly one frame (262 scanlines)."""
        cpu = self.cpu
        ppu = self.ppu

        for _ in range(262):
            # Run ~113 CPU cycles per scanline (341 PPU dots / 3)
            target_cycles = cpu.cycles + 113
            while cpu.cycles < target_cycles:
                cpu.step()

            # Advance PPU one scanline
            nmi = ppu.tick_scanline()
            if nmi:
                cpu.nmi()

        # Latch controller
        cpu.controller_shift[0] = cpu.controller_state[0]

    def render_frame(self):
        """Convert framebuffer to PhotoImage."""
        fb = self.ppu.framebuffer
        hex_pal = NES_HEX
        rows = []
        for y in range(self.HEIGHT):
            base = y * 256
            row = []
            for x in range(self.WIDTH):
                row.append(hex_pal[fb[base + x]])
            rows.append(row)

        # Write to PhotoImage
        # Using put() with row data for speed
        img = self.img
        for y in range(self.HEIGHT):
            row_data = "{" + " ".join(rows[y]) + "}"
            img.put(row_data, to=(0, y))

        # Scale
        self.scaled = img.zoom(self.SCALE, self.SCALE)
        self.canvas.itemconfig(self.img_id, image=self.scaled)

    def toggle_run(self):
        self.is_running = not self.is_running
        self.btn_run.config(text="STOP" if self.is_running else "RUN",
                           bg="#3a1a1a" if self.is_running else "#1a3a1a",
                           fg="#FF4444" if self.is_running else "#00FF00")
        if self.is_running:
            self.last_time = time.time()
            self.emulation_loop()

    def emulation_loop(self):
        if not self.is_running:
            return
        self.run_one_frame()
        self.render_frame()
        self.frame_count += 1

        now = time.time()
        dt = now - self.last_time
        if dt >= 1.0:
            self.fps = self.frame_count / dt
            self.frame_count = 0
            self.last_time = now
            self.lbl_fps.config(text=f"FPS: {self.fps:.1f}")

        self.update_status()
        self.root.after(1, self.emulation_loop)

    def step_frame(self):
        if self.rom_loaded:
            self.run_one_frame()
            self.render_frame()
            self.update_status()

    def update_status(self):
        c = self.cpu
        p = self.ppu
        self.lbl_regs.config(
            text=f"PC:{c.pc:04X} A:{c.a:02X} X:{c.x:02X} Y:{c.y:02X} SP:{c.sp:02X}")
        flags = ''.join([
            'N' if c.status & 0x80 else 'n',
            'V' if c.status & 0x40 else 'v',
            '-',
            'B' if c.status & 0x10 else 'b',
            'D' if c.status & 0x08 else 'd',
            'I' if c.status & 0x04 else 'i',
            'Z' if c.status & 0x02 else 'z',
            'C' if c.status & 0x01 else 'c',
        ])
        self.lbl_status.config(text=f"NV-BDIZC: {flags}")
        self.lbl_ppu.config(
            text=f"SL:{p.scanline:03d} FRM:{p.frame_count:06d}")
        self.lbl_scroll.config(
            text=f"V:{p.v:04X} T:{p.t:04X} FX:{p.fine_x} W:{p.w}")


if __name__ == "__main__":
    root = tk.Tk()
    app = ACHoldingsNesEmu(root)
    root.mainloop()
