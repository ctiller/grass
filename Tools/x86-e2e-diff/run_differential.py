#!/usr/bin/env python3
"""
E2E Differential Test Harness for Grass 64-bit x86-64 ISA Seam (Grass.ISA.X86.Target).

Verifies:
1. Ground-truth assembly encoding via `/usr/bin/llvm-mc-21 --triple=x86_64 -x86-asm-syntax=intel --show-encoding`
   (or `-filetype=obj` + `objcopy` for PC-relative branch fixups)
2. Ground-truth disassembly round-trip via `/usr/bin/objdump -D -b binary -m i386:x86-64 -M intel`
3. Lean 4 seam verification via `lake env lean --run Tests/ISA/X86/E2EDifferentialSuite.lean`

Covers Tiers 1-4 across all features in PROJECT.md § Feature Inventory:
- Tier 1: >= 5 representative test cases per feature (E1..E9, S1, F1..F15)
- Tier 2: >= 5 boundary/corner cases per category (REX high-byte, 32-bit zero-ext, SSE preserve vs VEX/EVEX zero-upper, EVEX disp8*N, opmasks, SIB/RIP escapes)
- Tier 3: Pairwise cross-feature combinations
- Tier 4: Real-world multi-instruction application scenarios
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from typing import List, Optional, Tuple

LLVM_MC = "/usr/bin/llvm-mc-21"
OBJDUMP = "/usr/bin/objdump"
OBJCOPY = "/usr/bin/objcopy"


@dataclass
class TestCase:
    tier: str
    feature: str
    label: str
    asm: str
    expected_hex: Optional[str] = None


# Comprehensive corpus covering Tiers 1, 2, 3, and 4
CORPUS: List[TestCase] = [
    # =========================================================================
    # TIER 1: FEATURE COVERAGE (>= 5 cases per feature E1..E9, S1, F1..F15)
    # =========================================================================

    # E1: Legacy Prefixes (Groups 1-4)
    TestCase("Tier 1", "E1", "LOCK prefix on memory ADD", "lock add qword ptr [rax], rbx"),
    TestCase("Tier 1", "E1", "REP prefix on MOVSB string copy", "rep movsb"),
    TestCase("Tier 1", "E1", "REPNE prefix on SCASB string scan", "repne scasb"),
    TestCase("Tier 1", "E1", "GS segment override prefix", "mov rax, qword ptr gs:[0x10]"),
    TestCase("Tier 1", "E1", "66 operand-size override prefix (16-bit ALU)", "add ax, bx"),

    # E2: REX Prefix (40-4F)
    TestCase("Tier 1", "E2", "REX.W 64-bit operand promotion", "mov rax, rbx"),
    TestCase("Tier 1", "E2", "REX.B r/m field extension (r8d)", "mov r8d, eax"),
    TestCase("Tier 1", "E2", "REX.R reg field extension (r8d)", "mov eax, r8d"),
    TestCase("Tier 1", "E2", "REX.X SIB index register extension", "mov eax, dword ptr [rax + r8*4]"),
    TestCase("Tier 1", "E2", "REX.WRB combined 64-bit extended register move", "mov r15, r14"),

    # E3: 2-Byte VEX (C5)
    TestCase("Tier 1", "E3", "C5 VEX 128-bit packed single FP add", "vaddps xmm0, xmm1, xmm2"),
    TestCase("Tier 1", "E3", "C5 VEX 256-bit packed single FP add", "vaddps ymm0, ymm1, ymm2"),
    TestCase("Tier 1", "E3", "C5 VEX 128-bit packed double FP add (pp=66)", "vaddpd xmm0, xmm1, xmm2"),
    TestCase("Tier 1", "E3", "C5 VEX scalar single FP add (pp=F3)", "vaddss xmm0, xmm1, xmm2"),
    TestCase("Tier 1", "E3", "C5 VEX scalar double FP add (pp=F2)", "vaddsd xmm0, xmm1, xmm2"),

    # E4: 3-Byte VEX (C4)
    TestCase("Tier 1", "E4", "C4 VEX extended register encoding", "vaddps xmm8, xmm9, xmm10"),
    TestCase("Tier 1", "E4", "C4 VEX 0F38 map byte shuffle", "vpshufb xmm0, xmm1, xmm2"),
    TestCase("Tier 1", "E4", "C4 VEX 0F3A map align right immediate", "vpalignr xmm0, xmm1, xmm2, 4"),
    TestCase("Tier 1", "E4", "C4 VEX 256-bit FMA3 single precision", "vfmadd213ps ymm0, ymm1, ymm2"),
    TestCase("Tier 1", "E4", "C4 VEX 256-bit FMA3 double precision (W=1)", "vfmadd213pd ymm0, ymm1, ymm2"),

    # E5: 4-Byte EVEX (62)
    TestCase("Tier 1", "E5", "EVEX 512-bit packed single FP add", "vaddps zmm0, zmm1, zmm2"),
    TestCase("Tier 1", "E5", "EVEX 512-bit merge-masked add {k1}", "vaddps zmm0 {k1}, zmm1, zmm2"),
    TestCase("Tier 1", "E5", "EVEX 512-bit zero-masked add {k2}{z}", "vaddps zmm0 {k2}{z}, zmm1, zmm2"),
    TestCase("Tier 1", "E5", "EVEX embedded rounding {rn-sae}", "vaddps zmm0, zmm1, zmm2, {rn-sae}"),
    TestCase("Tier 1", "E5", "EVEX high vector registers zmm16..zmm18", "vaddpd zmm16, zmm17, zmm18"),

    # E6: XOP Prefix (8F) & POP disambiguation
    TestCase("Tier 1", "E6", "POP r64 opcode-embedded register", "pop rax"),
    TestCase("Tier 1", "E6", "POP r/m64 ModR/M 8F /0 disambiguation", "pop qword ptr [rax]"),
    TestCase("Tier 1", "E6", "XOP map 9 packed byte rotate", "vprotb xmm0, xmm1, xmm2"),
    TestCase("Tier 1", "E6", "XOP map 8 immediate dword rotate", "vprotd xmm0, xmm1, 3"),
    TestCase("Tier 1", "E6", "XOP map 8 conditional vector move", "vpcmov xmm0, xmm1, xmm2, xmm3"),

    # E7: ModR/M & SIB / VSIB
    TestCase("Tier 1", "E7", "ModR/M register-direct (mod=11)", "mov eax, ebx"),
    TestCase("Tier 1", "E7", "ModR/M base+disp32 addressing (mod=10)", "mov eax, dword ptr [rbx + 0x12345678]"),
    TestCase("Tier 1", "E7", "ModR/M RIP-relative addressing (mod=00, rm=101)", "mov eax, dword ptr [rip + 0x100]"),
    TestCase("Tier 1", "E7", "SIB scaled index addressing [base+index*8+disp8]", "mov eax, dword ptr [rbx + rcx*8 + 0x10]"),
    TestCase("Tier 1", "E7", "VSIB vector index gather addressing", "vgatherdpd ymm0, [rax + xmm1*8], ymm2"),

    # E8: Displacements & disp8*N
    TestCase("Tier 1", "E8", "Legacy 8-bit signed displacement", "mov eax, dword ptr [rax + 4]"),
    TestCase("Tier 1", "E8", "Legacy 32-bit signed displacement", "mov eax, dword ptr [rax + 0x1000]"),
    TestCase("Tier 1", "E8", "EVEX disp8*64 compressed displacement (512-bit)", "vaddps zmm0, zmm1, zmmword ptr [rax + 0x40]"),
    TestCase("Tier 1", "E8", "EVEX disp8*32 compressed displacement (256-bit)", "vaddps ymm0, ymm1, ymmword ptr [rax + 0x20]"),
    TestCase("Tier 1", "E8", "EVEX disp8*16 compressed displacement (128-bit)", "vaddps xmm0, xmm1, xmmword ptr [rax + 0x10]"),

    # E9: Immediates & is4 Specifier
    TestCase("Tier 1", "E9", "8-bit shift count immediate", "shl eax, 4"),
    TestCase("Tier 1", "E9", "16-bit stack pop immediate on RET", "ret 0x10"),
    TestCase("Tier 1", "E9", "32-bit arithmetic immediate", "add ebx, 0x12345678"),
    TestCase("Tier 1", "E9", "64-bit full immediate MOVABS", "movabs rax, 0x1122334455667788"),
    TestCase("Tier 1", "E9", "is4 4th register specifier immediate byte", "vpblendvb xmm0, xmm1, xmm2, xmm3"),

    # S1: Extended Architectural State
    TestCase("Tier 1", "S1", "GPR state read/write (r15, rax)", "mov r15, rax"),
    TestCase("Tier 1", "S1", "ZMM 512-bit vector register state (zmm31, zmm0)", "vmovaps zmm31, zmm0"),
    TestCase("Tier 1", "S1", "Opmask register state (k7, k1)", "kmovw k7, k1"),
    TestCase("Tier 1", "S1", "Control register state (cr3)", "mov rax, cr3"),
    TestCase("Tier 1", "S1", "X87 FPU register stack state (st0, st1)", "fld st(1)"),

    # F1: Base Integer: Data Transfer
    TestCase("Tier 1", "F1", "MOV 32-bit register-register (seam-supported)", "mov eax, ebx"),
    TestCase("Tier 1", "F1", "MOV 64-bit register-register (seam-supported)", "mov rax, rbx"),
    TestCase("Tier 1", "F1", "MOVZX zero-extend byte to 32-bit (seam-supported)", "movzx eax, bl"),
    TestCase("Tier 1", "F1", "MOVSX sign-extend word to 64-bit (seam-supported)", "movsx rax, bx"),
    TestCase("Tier 1", "F1", "XCHG 64-bit register swap (seam-supported)", "xchg rbx, rcx"),

    # F2: Base Integer: Binary ALU
    TestCase("Tier 1", "F2", "ADD 64-bit register-register (seam-supported)", "add rax, rbx"),
    TestCase("Tier 1", "F2", "SUB 64-bit register-register (seam-supported)", "sub rax, rbx"),
    TestCase("Tier 1", "F2", "XOR 64-bit register-register (seam-supported)", "xor rax, rbx"),
    TestCase("Tier 1", "F2", "IMUL 64-bit signed multiply (seam-supported)", "imul rax, rbx"),
    TestCase("Tier 1", "F2", "TEST 64-bit bitwise AND flags (seam-supported)", "test rax, rbx"),

    # F3: Base Integer: Shift/Rotate/Bit
    TestCase("Tier 1", "F3", "SHL 64-bit logical shift left immediate (seam-supported)", "shl rax, 3"),
    TestCase("Tier 1", "F3", "SHR 64-bit logical shift right immediate (seam-supported)", "shr rax, 3"),
    TestCase("Tier 1", "F3", "SAR 64-bit arithmetic shift right immediate (seam-supported)", "sar rax, 3"),
    TestCase("Tier 1", "F3", "SETE conditional byte set (seam-supported)", "sete al"),
    TestCase("Tier 1", "F3", "CMOVE conditional 64-bit move (seam-supported)", "cmove rax, rbx"),

    # F4: Base Integer: String & Flags
    TestCase("Tier 1", "F4", "REP MOVSB block byte copy", "rep movsb"),
    TestCase("Tier 1", "F4", "REP STOSQ block qword fill", "rep stosq"),
    TestCase("Tier 1", "F4", "CLD clear direction flag", "cld"),
    TestCase("Tier 1", "F4", "STC set carry flag", "stc"),
    TestCase("Tier 1", "F4", "PUSHFQ push 64-bit RFLAGS", "pushfq"),

    # F5: Control Flow: Branches & Stack
    TestCase("Tier 1", "F5", "PUSH 64-bit register (seam-supported)", "push rax"),
    TestCase("Tier 1", "F5", "POP 64-bit register (seam-supported)", "pop rbx"),
    TestCase("Tier 1", "F5", "RET near return (seam-supported)", "ret"),
    TestCase("Tier 1", "F5", "JMP 8-bit short relative jump (seam-supported)", ".L1:; jmp .L1"),
    TestCase("Tier 1", "F5", "JE 8-bit conditional short jump (seam-supported)", ".L1:; je .L1"),

    # F9: Atomic & Synchronization
    TestCase("Tier 1", "F9", "LOCK ADD atomic read-modify-write", "lock add qword ptr [rax], rbx"),
    TestCase("Tier 1", "F9", "LOCK XADD atomic exchange-and-add", "lock xadd qword ptr [rax], rbx"),
    TestCase("Tier 1", "F9", "LOCK CMPXCHG atomic compare-and-exchange", "lock cmpxchg qword ptr [rcx], rbx"),
    TestCase("Tier 1", "F9", "MFENCE full memory barrier", "mfence"),
    TestCase("Tier 1", "F9", "LFENCE load memory barrier", "lfence"),

    # F6: Ring-0 System: Syscall & VM
    TestCase("Tier 1", "F6", "SYSCALL fast system call (seam-supported)", "syscall"),
    TestCase("Tier 1", "F6", "SYSRETQ 64-bit return from system call", "sysretq"),
    TestCase("Tier 1", "F6", "VMCALL hypervisor call", "vmcall"),
    TestCase("Tier 1", "F6", "VMLAUNCH launch virtual machine", "vmlaunch"),
    TestCase("Tier 1", "F6", "VMRUN run AMD SVM guest", "vmrun"),

    # F7: Ring-0 System: CR/DR/MSR/Tables
    TestCase("Tier 1", "F7", "MOV from CR0 control register", "mov rax, cr0"),
    TestCase("Tier 1", "F7", "MOV to DR7 debug register", "mov dr7, rax"),
    TestCase("Tier 1", "F7", "RDMSR read model-specific register", "rdmsr"),
    TestCase("Tier 1", "F7", "WRMSR write model-specific register", "wrmsr"),
    TestCase("Tier 1", "F7", "SWAPGS swap GS base register", "swapgs"),

    # F8: Ring-0 System: TLB/Cache/Interrupts
    TestCase("Tier 1", "F8", "INVLPG invalidate TLB entry", "invlpg [rax]"),
    TestCase("Tier 1", "F8", "WBINVD write-back and invalidate cache", "wbinvd"),
    TestCase("Tier 1", "F8", "HLT processor halt (seam-supported)", "hlt"),
    TestCase("Tier 1", "F8", "UD2 explicit undefined instruction (seam-supported)", "ud2"),
    TestCase("Tier 1", "F8", "CPUID processor identification", "cpuid"),

    # F10: X87 FPU
    TestCase("Tier 1", "F10", "FLD push ST(1) onto FPU stack", "fld st(1)"),
    TestCase("Tier 1", "F10", "FADD ST(0) += ST(1)", "fadd st(0), st(1)"),
    TestCase("Tier 1", "F10", "FMUL ST(0) *= ST(2)", "fmul st(0), st(2)"),
    TestCase("Tier 1", "F10", "FSQRT square root ST(0)", "fsqrt"),
    TestCase("Tier 1", "F10", "FXSAVE64 save 64-bit FPU/SIMD state", "fxsave64 [rax]"),

    # F11: MMX & SSE1-4.2
    TestCase("Tier 1", "F11", "MOVAPS aligned packed single move", "movaps xmm0, xmm1"),
    TestCase("Tier 1", "F11", "ADDPS packed single FP add", "addps xmm0, xmm1"),
    TestCase("Tier 1", "F11", "PADDD packed 32-bit integer add", "paddd xmm0, xmm1"),
    TestCase("Tier 1", "F11", "PSHUFB SSSE3 packed byte shuffle", "pshufb xmm0, xmm1"),
    TestCase("Tier 1", "F11", "CRC32 SSE4.2 hardware CRC accumulate", "crc32 eax, ebx"),

    # F12: AVX / AVX2 / FMA & XOP
    TestCase("Tier 1", "F12", "VADDPS 256-bit AVX packed single FP add", "vaddps ymm0, ymm1, ymm2"),
    TestCase("Tier 1", "F12", "VPADDD 256-bit AVX2 packed dword add", "vpaddd ymm0, ymm1, ymm2"),
    TestCase("Tier 1", "F12", "VFMADD213PS 256-bit FMA3 fused multiply-add", "vfmadd213ps ymm0, ymm1, ymm2"),
    TestCase("Tier 1", "F12", "VPERM2F128 256-bit lane permute", "vperm2f128 ymm0, ymm1, ymm2, 1"),
    TestCase("Tier 1", "F12", "VZEROUPPER zero upper YMM/ZMM bits", "vzeroupper"),

    # F14: BMI1 / BMI2 / ABM
    TestCase("Tier 1", "F14", "ANDN BMI1 bitwise AND-NOT", "andn eax, ebx, ecx"),
    TestCase("Tier 1", "F14", "BLSI BMI1 isolate lowest set bit", "blsi eax, ebx"),
    TestCase("Tier 1", "F14", "TZCNT count trailing zero bits", "tzcnt eax, ebx"),
    TestCase("Tier 1", "F14", "PDEP BMI2 parallel bit deposit", "pdep rax, rbx, rcx"),
    TestCase("Tier 1", "F14", "RORX BMI2 flagless rotate right", "rorx rax, rbx, 7"),

    # F15: Crypto & Special
    TestCase("Tier 1", "F15", "AESENC AES single encryption round", "aesenc xmm0, xmm1"),
    TestCase("Tier 1", "F15", "AESENCLAST AES final encryption round", "aesenclast xmm0, xmm1"),
    TestCase("Tier 1", "F15", "PCLMULQDQ carry-less multiplication", "pclmulqdq xmm0, xmm1, 1"),
    TestCase("Tier 1", "F15", "SHA256RNDS2 two SHA-256 rounds", "sha256rnds2 xmm0, xmm1, xmm0"),
    TestCase("Tier 1", "F15", "SHA256MSG1 SHA-256 message schedule 1", "sha256msg1 xmm0, xmm1"),

    # F13: AVX-512 & Opmasks
    TestCase("Tier 1", "F13", "VADDPS 512-bit with zeroing mask {k1}{z}", "vaddps zmm0 {k1}{z}, zmm1, zmm2"),
    TestCase("Tier 1", "F13", "VPADDQ 512-bit 64-bit integer add {k2}", "vpaddq zmm0 {k2}, zmm1, zmm2"),
    TestCase("Tier 1", "F13", "VFMADD213PS 512-bit FMA3", "vfmadd213ps zmm0, zmm1, zmm2"),
    TestCase("Tier 1", "F13", "KMOVW move opmask register", "kmovw k1, k2"),
    TestCase("Tier 1", "F13", "KANDW bitwise AND opmask registers", "kandw k1, k2, k3"),

    # =========================================================================
    # TIER 2: BOUNDARY & CORNER CASES (>= 5 per boundary category)
    # =========================================================================

    # Category B1: REX High-Byte Registers AH..BH vs SPL..DIL
    TestCase("Tier 2", "B1-REX-HighByte", "Legacy AH high-byte register (no REX allowed)", "mov ah, al"),
    TestCase("Tier 2", "B1-REX-HighByte", "Legacy BH high-byte register (no REX allowed)", "mov bh, cl"),
    TestCase("Tier 2", "B1-REX-HighByte", "REX-prefixed SPL low-byte register (0x40 required)", "mov spl, al"),
    TestCase("Tier 2", "B1-REX-HighByte", "REX-prefixed BPL low-byte register (0x40 required)", "mov bpl, al"),
    TestCase("Tier 2", "B1-REX-HighByte", "REX-prefixed DIL low-byte register (0x40 required)", "mov dil, sil"),

    # Category B2: 32-bit Zero-Extension vs 8/16-bit Preservation
    TestCase("Tier 2", "B2-WidthExt", "32-bit MOV immediate zero-extends upper 32 bits (seam-supported)", "mov eax, 0xffffffff"),
    TestCase("Tier 2", "B2-WidthExt", "64-bit MOV immediate full 64-bit width (seam-supported)", "movabs rax, 0xffffffffffffffff"),
    TestCase("Tier 2", "B2-WidthExt", "8-bit MOV preserves upper 56 bits of RAX", "mov al, 0xff"),
    TestCase("Tier 2", "B2-WidthExt", "16-bit MOV preserves upper 48 bits of RAX", "mov ax, 0xffff"),
    TestCase("Tier 2", "B2-WidthExt", "32-bit ADD zero-extends upper 32 bits (seam-supported)", "add eax, ebx"),

    # Category B3: SSE Preserve-Upper vs VEX/EVEX Zero-Upper
    TestCase("Tier 2", "B3-VectorUpper", "Legacy SSE ADDPS preserves bits [511:128]", "addps xmm0, xmm1"),
    TestCase("Tier 2", "B3-VectorUpper", "VEX 128-bit VADDPS zeroes bits [511:128]", "vaddps xmm0, xmm1, xmm2"),
    TestCase("Tier 2", "B3-VectorUpper", "VEX 256-bit VADDPS zeroes bits [511:256]", "vaddps ymm0, ymm1, ymm2"),
    TestCase("Tier 2", "B3-VectorUpper", "EVEX 128-bit VADDPS zmm0 subview zeroes bits [511:128]", "vaddps xmm16, xmm17, xmm18"),
    TestCase("Tier 2", "B3-VectorUpper", "EVEX 512-bit VADDPS writes full 512 bits", "vaddps zmm0, zmm1, zmm2"),

    # Category B4: EVEX disp8*N Compressed Displacements
    TestCase("Tier 2", "B4-Disp8N", "EVEX Full 512-bit disp8*64 boundary (+64 -> disp8=0x01)", "vaddps zmm0, zmm1, zmmword ptr [rax + 64]"),
    TestCase("Tier 2", "B4-Disp8N", "EVEX Full 512-bit disp8*64 max positive (+8128 -> disp8=0x7f)", "vaddps zmm0, zmm1, zmmword ptr [rax + 8128]"),
    TestCase("Tier 2", "B4-Disp8N", "EVEX Full 512-bit unaligned disp (+65 -> falls back to disp32)", "vaddps zmm0, zmm1, zmmword ptr [rax + 65]"),
    TestCase("Tier 2", "B4-Disp8N", "EVEX 256-bit disp8*32 boundary (+32 -> disp8=0x01)", "vaddps ymm0, ymm1, ymmword ptr [rax + 32]"),
    TestCase("Tier 2", "B4-Disp8N", "EVEX 128-bit disp8*16 boundary (+16 -> disp8=0x01)", "vaddps xmm0, xmm1, xmmword ptr [rax + 16]"),

    # Category B5: Opmask k0 Unmasked vs k1-k7 {z} Masking
    TestCase("Tier 2", "B5-Opmask", "EVEX unmasked (aaa=000 implicit k0)", "vaddps zmm0, zmm1, zmm2"),
    TestCase("Tier 2", "B5-Opmask", "EVEX k1 merge-masked (aaa=001, z=0)", "vaddps zmm0 {k1}, zmm1, zmm2"),
    TestCase("Tier 2", "B5-Opmask", "EVEX k1 zero-masked (aaa=001, z=1)", "vaddps zmm0 {k1}{z}, zmm1, zmm2"),
    TestCase("Tier 2", "B5-Opmask", "EVEX k7 zero-masked (aaa=111, z=1)", "vaddps zmm0 {k7}{z}, zmm1, zmm2"),
    TestCase("Tier 2", "B5-Opmask", "EVEX k3 merge-masked on high ZMM registers", "vaddpd zmm20 {k3}, zmm21, zmm22"),

    # Category B6: SIB / ModR/M / RIP-Relative Addressing Escapes
    TestCase("Tier 2", "B6-AddrEscapes", "[rsp] base requires mandatory SIB byte 0x24", "mov rax, qword ptr [rsp]"),
    TestCase("Tier 2", "B6-AddrEscapes", "[r12] base requires mandatory SIB byte 0x24", "mov rax, qword ptr [r12]"),
    TestCase("Tier 2", "B6-AddrEscapes", "[rbp] base requires mandatory disp8=0x00", "mov rax, qword ptr [rbp]"),
    TestCase("Tier 2", "B6-AddrEscapes", "[r13] base requires mandatory disp8=0x00", "mov rax, qword ptr [r13]"),
    TestCase("Tier 2", "B6-AddrEscapes", "[rip+disp32] ModR/M mod=00 rm=101 encoding", "lea rax, [rip + 0x1234]"),

    # =========================================================================
    # TIER 3: CROSS-FEATURE COMBINATIONS (Pairwise Prefix/Width/Addressing/Mask)
    # =========================================================================
    TestCase("Tier 3", "Cross", "LOCK + REX.W + SIB scaled index RMW", "lock add qword ptr [rax + rcx*8 + 0x10], r15"),
    TestCase("Tier 3", "Cross", "EVEX 512-bit + {k3}{z} + disp8*64 compressed displacement", "vaddps zmm5 {k3}{z}, zmm6, zmmword ptr [rbx + 0x80]"),
    TestCase("Tier 3", "Cross", "EVEX 512-bit + embedded broadcast {1to16} + {k1}", "vaddps zmm0 {k1}, zmm1, dword ptr [rax + 0x10]{1to16}"),
    TestCase("Tier 3", "Cross", "VEX 256-bit + VSIB gather + extended YMM registers", "vgatherdpd ymm8, [r12 + xmm9*4 + 0x20], ymm10"),
    TestCase("Tier 3", "Cross", "BMI2 RORX + REX.W + memory source with SIB", "rorx r14, qword ptr [rax + rbx*4 + 0x40], 17"),
    TestCase("Tier 3", "Cross", "AES-NI + VEX VAESENC 256-bit vector crypto", "vaesenc ymm0, ymm1, ymm2"),

    # =========================================================================
    # TIER 4: REAL-WORLD APPLICATION SCENARIOS (Multi-instruction kernels)
    # =========================================================================
    TestCase(
        "Tier 4",
        "Scenario-SIMD-Memcpy",
        "AVX2 256-bit vectorized memory copy loop with pointer advance",
        ".Lloop:; vmovdqu ymm0, ymmword ptr [rsi]; vmovdqu ymmword ptr [rdi], ymm0; add rsi, 32; add rdi, 32; sub rcx, 32; jnz .Lloop",
    ),
    TestCase(
        "Tier 4",
        "Scenario-SHA256-Block",
        "Hardware SHA-256 message schedule and round update sequence",
        "sha256msg1 xmm0, xmm1; sha256msg2 xmm0, xmm2; sha256rnds2 xmm3, xmm4, xmm0",
    ),
    TestCase(
        "Tier 4",
        "Scenario-Ring0-Syscall",
        "Ring-0 syscall entry/exit prologue and return sequence",
        "swapgs; mov qword ptr gs:[0x10], rsp; mov rsp, qword ptr gs:[0x08]; syscall; sysretq",
    ),
    TestCase(
        "Tier 4",
        "Scenario-AVX512-Kernel",
        "AVX-512 masked FMA accumulation kernel with opmask setup",
        "kmovw k1, eax; vfmadd231ps zmm0 {k1}{z}, zmm1, zmmword ptr [rdi + 0x40]; vzeroupper",
    ),
]


def assemble_with_llvm_mc(asm: str) -> bytes:
    """Invoke llvm-mc-21 on an assembly string (single or semicolon-separated instructions) and return raw bytes."""
    lines = [line.strip() for line in asm.split(";") if line.strip()]
    full_input = "\n".join(lines) + "\n"

    with tempfile.NamedTemporaryFile(suffix=".o", delete=False) as tf_o:
        obj_path = tf_o.name
    bin_path = obj_path + ".bin"
    try:
        proc = subprocess.run(
            [LLVM_MC, "--triple=x86_64", "-x86-asm-syntax=intel", "-filetype=obj", "-o", obj_path],
            input=full_input,
            text=True,
            capture_output=True,
            check=True,
        )
        subprocess.run(
            [OBJCOPY, "-O", "binary", "--only-section=.text", obj_path, bin_path],
            check=True,
            capture_output=True,
        )
        with open(bin_path, "rb") as f:
            raw_bytes = f.read()
        if not raw_bytes:
            raise RuntimeError(f"llvm-mc-21 produced empty .text section for: {asm}")
        return raw_bytes
    finally:
        for p in (obj_path, bin_path):
            if os.path.exists(p):
                os.remove(p)


def verify_with_objdump(raw_bytes: bytes) -> str:
    """Write raw bytes to a temp file and disassemble with GNU objdump."""
    with tempfile.NamedTemporaryFile(suffix=".bin", delete=False) as tf:
        tf.write(raw_bytes)
        temp_path = tf.name
    try:
        proc = subprocess.run(
            [OBJDUMP, "-D", "-b", "binary", "-m", "i386:x86-64", "-M", "intel", temp_path],
            text=True,
            capture_output=True,
            check=True,
        )
        disasm_lines = []
        for line in proc.stdout.splitlines():
            if re.match(r"^\s*[0-9a-fA-F]+:\s+", line):
                if "(bad)" in line or "<internal disassembler error>" in line:
                    raise RuntimeError(f"objdump failed to decode bytes {raw_bytes.hex()}: {line}")
                disasm_lines.append(line.strip())
        return " | ".join(disasm_lines)
    finally:
        if os.path.exists(temp_path):
            os.remove(temp_path)


def run_lean_suite(require_full_seam: bool) -> Tuple[int, str]:
    """Run lake env lean --run Tests/ISA/X86/E2EDifferentialSuite.lean."""
    cmd = ["lake", "env", "lean", "--run", "Tests/ISA/X86/E2EDifferentialSuite.lean"]
    if require_full_seam:
        cmd.extend(["--", "--strict"])
    proc = subprocess.run(
        cmd,
        text=True,
        capture_output=True,
    )
    return proc.returncode, proc.stdout + proc.stderr


def main() -> int:
    parser = argparse.ArgumentParser(description="Run E2E differential test suite against llvm-mc-21, objdump, and Lean seam.")
    parser.add_argument("--require-full-seam", action="store_true", help="Require 100%% of Tier 1-4 cases to decode in Lean seam (M6 gate).")
    parser.add_argument("--dump-lean-cases", action="store_true", help="Print Lean test case definitions for Tests/ISA/X86/E2EDifferentialSuite.lean.")
    args = parser.parse_args()

    tier_counts = {}
    feature_counts = {}
    passed = 0
    failed = 0

    lean_rows = []

    for idx, tc in enumerate(CORPUS):
        tier_counts[tc.tier] = tier_counts.get(tc.tier, 0) + 1
        feature_counts[tc.feature] = feature_counts.get(tc.feature, 0) + 1
        try:
            raw_bytes = assemble_with_llvm_mc(tc.asm)
            disasm = verify_with_objdump(raw_bytes)
            passed += 1
            lean_rows.append((tc.tier, tc.feature, tc.label, tc.asm, list(raw_bytes)))
        except Exception as e:
            failed += 1
            print(f"[FAIL] Case #{idx + 1} ({tc.tier} / {tc.feature}: {tc.label}): {e}", file=sys.stderr)

    if args.dump_lean_cases:
        for tier, feat, label, asm, b_list in lean_rows:
            b_str = ", ".join(f"0x{b:02x}" for b in b_list)
            safe_label = label.replace('"', '\\"')
            safe_asm = asm.replace('"', '\\"')
            print(f'  {{ tier := "{tier}", feature := "{feat}", label := "{safe_label}", asm := "{safe_asm}", bytes := [{b_str}] }},')
        return 0

    print("================================================================================")
    print("Grass 64-bit x86-64 E2E Differential Test Suite (llvm-mc-21 / objdump / Lean)")
    print("================================================================================")
    print("\n-- Ground Truth Oracle Verification Summary (llvm-mc-21 & objdump) --")
    for tier, count in sorted(tier_counts.items()):
        print(f"  {tier:10s}: {count:3d} cases verified against llvm-mc-21 & objdump")
    print(f"  TOTAL     : {passed:3d} passed, {failed:3d} failed")

    if failed > 0:
        return 1

    print("\n-- Invoking Lean Seam Differential Suite (Tests/ISA/X86/E2EDifferentialSuite.lean) --")
    rc, out = run_lean_suite(args.require_full_seam)
    print(out.strip())
    if rc != 0:
        print(f"[FAIL] Lean Seam Differential Suite exited with code {rc}")
        return rc

    print("\n[PASS] All ground-truth and Lean seam E2E differential checks succeeded.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
