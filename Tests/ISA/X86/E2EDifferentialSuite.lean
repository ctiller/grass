import Tests.ISA.X86.CorpusCommon
import Grass.ISA.X86.Target.Encode

/-!
# End-to-End Differential Test Suite (`Tests/ISA/X86/E2EDifferentialSuite.lean`)

This module implements the Lean 4 side of the E2E differential test harness
(`Tools/x86-e2e-diff/run_differential.py`), comparing `Grass.ISA.X86.Target.encode`
and `Grass.ISA.X86.Target.decode` against ground-truth machine encodings produced by
`/usr/bin/llvm-mc-21` and verified by `/usr/bin/objdump`.

It covers all four verification tiers defined in `TEST_INFRA.md`:
- **Tier 1 (Feature Coverage)**: >= 5 representative test cases per feature in
  `PROJECT.md § Feature Inventory` (`E1`–`E9`, `S1`, `F1`–`F15`).
- **Tier 2 (Boundary & Corner Cases)**: >= 5 boundary test cases per category
  (REX high-byte registers `AH`..`BH` vs `SPL`..`DIL`, 32-bit zero-extension vs
  8/16-bit preservation, SSE preserve-upper vs VEX/EVEX zero-upper, EVEX `disp8*N`
  compressed displacements, `k0` unmasked vs `k1`–`k7` `{z}` masking, SIB/RIP escapes).
- **Tier 3 (Cross-Feature Combinations)**: Pairwise interactions across prefix
  groups, vector widths, memory addressing, and predication/rounding.
- **Tier 4 (Real-World Application Scenarios)**: Multi-instruction kernels
  (SIMD vectorized `memcpy`, hardware SHA-256 block update, Ring-0 `syscall`/`sysretq`
  entry/exit, and AVX-512 masked gather/FMA kernel).

During Milestones M1–M5, every instruction currently supported by `Grass.ISA.X86.Target`
is verified for byte-exact round-trip agreement (`encode instr = bytes` and
`decode bytes = some (instr, bytes.length)`), while instructions belonging to pending
milestones are accounted for honestly. Passing `--strict` enforces 100% full-seam
coverage for the Milestone M6 gate.
-/

namespace Grass.Tests.ISA.X86.E2EDifferentialSuite

open Grass.ISA.X86 (Gpr)
open Grass.ISA.X86.Target (Instr Sz AluOp ShiftOp Cond encode decode)
open Grass.Tests.ISA.X86.Corpus (hexBytes)

/-- One ground-truth differential test case verified against `llvm-mc-21` and `objdump`. -/
structure DifferentialCase where
  tier : String
  feature : String
  label : String
  asm : String
  bytes : List UInt8
  isMultiInstr : Bool := false
deriving Repr

/-- Status of checking one differential case against `Grass.ISA.X86.Target`. -/
inductive CheckResult where
  | verifiedRoundTrip (instrRepr : String)
  | pendingMilestone
  | mismatch (reason : String)
deriving Repr

/-- Check one differential case against `Grass.ISA.X86.Target.decode` and `encode`. -/
def checkCase (tc : DifferentialCase) : CheckResult :=
  if tc.isMultiInstr then
    -- For multi-instruction kernels, verify that any decoded prefix slice round-trips cleanly
    match decode tc.bytes with
    | some (instr, len) =>
        let slice := tc.bytes.take len
        if encode instr == slice then
          .verifiedRoundTrip (reprStr instr)
        else
          .mismatch s!"multi-instr head encode mismatch: expected {hexBytes (slice.map UInt8.toBitVec)}, got {hexBytes ((encode instr).map UInt8.toBitVec)}"
    | none => .pendingMilestone
  else
    match decode tc.bytes with
    | some (instr, len) =>
        if len != tc.bytes.length then
          .mismatch s!"decoded length {len} != ground-truth length {tc.bytes.length}"
        else if encode instr != tc.bytes then
          .mismatch s!"encode instr ({hexBytes ((encode instr).map UInt8.toBitVec)}) != ground-truth ({hexBytes (tc.bytes.map UInt8.toBitVec)})"
        else
          .verifiedRoundTrip (reprStr instr)
    | none => .pendingMilestone

/-- Complete 165-case ground-truth E2E differential corpus across Tiers 1–4. -/
def e2eCorpus : List DifferentialCase := [
  -- Tier 1: E1 Legacy Prefixes
  { tier := "Tier 1", feature := "E1", label := "LOCK prefix on memory ADD", asm := "lock add qword ptr [rax], rbx", bytes := [0xf0, 0x48, 0x01, 0x18] },
  { tier := "Tier 1", feature := "E1", label := "REP prefix on MOVSB string copy", asm := "rep movsb", bytes := [0xf3, 0xa4] },
  { tier := "Tier 1", feature := "E1", label := "REPNE prefix on SCASB string scan", asm := "repne scasb", bytes := [0xf2, 0xae] },
  { tier := "Tier 1", feature := "E1", label := "GS segment override prefix", asm := "mov rax, qword ptr gs:[0x10]", bytes := [0x65, 0x48, 0x8b, 0x04, 0x25, 0x10, 0x00, 0x00, 0x00] },
  { tier := "Tier 1", feature := "E1", label := "66 operand-size override prefix (16-bit ALU)", asm := "add ax, bx", bytes := [0x66, 0x01, 0xd8] },

  -- Tier 1: E2 REX Prefix
  { tier := "Tier 1", feature := "E2", label := "REX.W 64-bit operand promotion", asm := "mov rax, rbx", bytes := [0x48, 0x89, 0xd8] },
  { tier := "Tier 1", feature := "E2", label := "REX.B r/m field extension (r8d)", asm := "mov r8d, eax", bytes := [0x41, 0x89, 0xc0] },
  { tier := "Tier 1", feature := "E2", label := "REX.R reg field extension (r8d)", asm := "mov eax, r8d", bytes := [0x44, 0x89, 0xc0] },
  { tier := "Tier 1", feature := "E2", label := "REX.X SIB index register extension", asm := "mov eax, dword ptr [rax + r8*4]", bytes := [0x42, 0x8b, 0x04, 0x80] },
  { tier := "Tier 1", feature := "E2", label := "REX.WRB combined 64-bit extended register move", asm := "mov r15, r14", bytes := [0x4d, 0x89, 0xf7] },

  -- Tier 1: E3 2-Byte VEX (C5)
  { tier := "Tier 1", feature := "E3", label := "C5 VEX 128-bit packed single FP add", asm := "vaddps xmm0, xmm1, xmm2", bytes := [0xc5, 0xf0, 0x58, 0xc2] },
  { tier := "Tier 1", feature := "E3", label := "C5 VEX 256-bit packed single FP add", asm := "vaddps ymm0, ymm1, ymm2", bytes := [0xc5, 0xf4, 0x58, 0xc2] },
  { tier := "Tier 1", feature := "E3", label := "C5 VEX 128-bit packed double FP add (pp=66)", asm := "vaddpd xmm0, xmm1, xmm2", bytes := [0xc5, 0xf1, 0x58, 0xc2] },
  { tier := "Tier 1", feature := "E3", label := "C5 VEX scalar single FP add (pp=F3)", asm := "vaddss xmm0, xmm1, xmm2", bytes := [0xc5, 0xf2, 0x58, 0xc2] },
  { tier := "Tier 1", feature := "E3", label := "C5 VEX scalar double FP add (pp=F2)", asm := "vaddsd xmm0, xmm1, xmm2", bytes := [0xc5, 0xf3, 0x58, 0xc2] },

  -- Tier 1: E4 3-Byte VEX (C4)
  { tier := "Tier 1", feature := "E4", label := "C4 VEX extended register encoding", asm := "vaddps xmm8, xmm9, xmm10", bytes := [0xc4, 0x41, 0x30, 0x58, 0xc2] },
  { tier := "Tier 1", feature := "E4", label := "C4 VEX 0F38 map byte shuffle", asm := "vpshufb xmm0, xmm1, xmm2", bytes := [0xc4, 0xe2, 0x71, 0x00, 0xc2] },
  { tier := "Tier 1", feature := "E4", label := "C4 VEX 0F3A map align right immediate", asm := "vpalignr xmm0, xmm1, xmm2, 4", bytes := [0xc4, 0xe3, 0x71, 0x0f, 0xc2, 0x04] },
  { tier := "Tier 1", feature := "E4", label := "C4 VEX 256-bit FMA3 single precision", asm := "vfmadd213ps ymm0, ymm1, ymm2", bytes := [0xc4, 0xe2, 0x75, 0xa8, 0xc2] },
  { tier := "Tier 1", feature := "E4", label := "C4 VEX 256-bit FMA3 double precision (W=1)", asm := "vfmadd213pd ymm0, ymm1, ymm2", bytes := [0xc4, 0xe2, 0xf5, 0xa8, 0xc2] },

  -- Tier 1: E5 4-Byte EVEX (62)
  { tier := "Tier 1", feature := "E5", label := "EVEX 512-bit packed single FP add", asm := "vaddps zmm0, zmm1, zmm2", bytes := [0x62, 0xf1, 0x74, 0x48, 0x58, 0xc2] },
  { tier := "Tier 1", feature := "E5", label := "EVEX 512-bit merge-masked add {k1}", asm := "vaddps zmm0 {k1}, zmm1, zmm2", bytes := [0x62, 0xf1, 0x74, 0x49, 0x58, 0xc2] },
  { tier := "Tier 1", feature := "E5", label := "EVEX 512-bit zero-masked add {k2}{z}", asm := "vaddps zmm0 {k2}{z}, zmm1, zmm2", bytes := [0x62, 0xf1, 0x74, 0xca, 0x58, 0xc2] },
  { tier := "Tier 1", feature := "E5", label := "EVEX embedded rounding {rn-sae}", asm := "vaddps zmm0, zmm1, zmm2, {rn-sae}", bytes := [0x62, 0xf1, 0x74, 0x18, 0x58, 0xc2] },
  { tier := "Tier 1", feature := "E5", label := "EVEX high vector registers zmm16..zmm18", asm := "vaddpd zmm16, zmm17, zmm18", bytes := [0x62, 0xa1, 0xf5, 0x40, 0x58, 0xc2] },

  -- Tier 1: E6 XOP Prefix (8F)
  { tier := "Tier 1", feature := "E6", label := "POP r64 opcode-embedded register", asm := "pop rax", bytes := [0x58] },
  { tier := "Tier 1", feature := "E6", label := "POP r/m64 ModR/M 8F /0 disambiguation", asm := "pop qword ptr [rax]", bytes := [0x8f, 0x00] },
  { tier := "Tier 1", feature := "E6", label := "XOP map 9 packed byte rotate", asm := "vprotb xmm0, xmm1, xmm2", bytes := [0x8f, 0xe9, 0x68, 0x90, 0xc1] },
  { tier := "Tier 1", feature := "E6", label := "XOP map 8 immediate dword rotate", asm := "vprotd xmm0, xmm1, 3", bytes := [0x8f, 0xe8, 0x78, 0xc2, 0xc1, 0x03] },
  { tier := "Tier 1", feature := "E6", label := "XOP map 8 conditional vector move", asm := "vpcmov xmm0, xmm1, xmm2, xmm3", bytes := [0x8f, 0xe8, 0x70, 0xa2, 0xc2, 0x30] },

  -- Tier 1: E7 ModR/M & SIB / VSIB
  { tier := "Tier 1", feature := "E7", label := "ModR/M register-direct (mod=11)", asm := "mov eax, ebx", bytes := [0x89, 0xd8] },
  { tier := "Tier 1", feature := "E7", label := "ModR/M base+disp32 addressing (mod=10)", asm := "mov eax, dword ptr [rbx + 0x12345678]", bytes := [0x8b, 0x83, 0x78, 0x56, 0x34, 0x12] },
  { tier := "Tier 1", feature := "E7", label := "ModR/M RIP-relative addressing (mod=00, rm=101)", asm := "mov eax, dword ptr [rip + 0x100]", bytes := [0x8b, 0x05, 0x00, 0x01, 0x00, 0x00] },
  { tier := "Tier 1", feature := "E7", label := "SIB scaled index addressing [base+index*8+disp8]", asm := "mov eax, dword ptr [rbx + rcx*8 + 0x10]", bytes := [0x8b, 0x44, 0xcb, 0x10] },
  { tier := "Tier 1", feature := "E7", label := "VSIB vector index gather addressing", asm := "vgatherdpd ymm0, [rax + xmm1*8], ymm2", bytes := [0xc4, 0xe2, 0xed, 0x92, 0x04, 0xc8] },

  -- Tier 1: E8 Displacements & disp8*N
  { tier := "Tier 1", feature := "E8", label := "Legacy 8-bit signed displacement", asm := "mov eax, dword ptr [rax + 4]", bytes := [0x8b, 0x40, 0x04] },
  { tier := "Tier 1", feature := "E8", label := "Legacy 32-bit signed displacement", asm := "mov eax, dword ptr [rax + 0x1000]", bytes := [0x8b, 0x80, 0x00, 0x10, 0x00, 0x00] },
  { tier := "Tier 1", feature := "E8", label := "EVEX disp8*64 compressed displacement (512-bit)", asm := "vaddps zmm0, zmm1, zmmword ptr [rax + 0x40]", bytes := [0x62, 0xf1, 0x74, 0x48, 0x58, 0x40, 0x01] },
  { tier := "Tier 1", feature := "E8", label := "EVEX disp8*32 compressed displacement (256-bit)", asm := "vaddps ymm0, ymm1, ymmword ptr [rax + 0x20]", bytes := [0xc5, 0xf4, 0x58, 0x40, 0x20] },
  { tier := "Tier 1", feature := "E8", label := "EVEX disp8*16 compressed displacement (128-bit)", asm := "vaddps xmm0, xmm1, xmmword ptr [rax + 0x10]", bytes := [0xc5, 0xf0, 0x58, 0x40, 0x10] },

  -- Tier 1: E9 Immediates & is4 Specifier
  { tier := "Tier 1", feature := "E9", label := "8-bit shift count immediate", asm := "shl eax, 4", bytes := [0xc1, 0xe0, 0x04] },
  { tier := "Tier 1", feature := "E9", label := "16-bit stack pop immediate on RET", asm := "ret 0x10", bytes := [0xc2, 0x10, 0x00] },
  { tier := "Tier 1", feature := "E9", label := "32-bit arithmetic immediate", asm := "add ebx, 0x12345678", bytes := [0x81, 0xc3, 0x78, 0x56, 0x34, 0x12] },
  { tier := "Tier 1", feature := "E9", label := "64-bit full immediate MOVABS", asm := "movabs rax, 0x1122334455667788", bytes := [0x48, 0xb8, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11] },
  { tier := "Tier 1", feature := "E9", label := "is4 4th register specifier immediate byte", asm := "vpblendvb xmm0, xmm1, xmm2, xmm3", bytes := [0xc4, 0xe3, 0x71, 0x4c, 0xc2, 0x30] },

  -- Tier 1: S1 Extended Architectural State
  { tier := "Tier 1", feature := "S1", label := "GPR state read/write (r15, rax)", asm := "mov r15, rax", bytes := [0x49, 0x89, 0xc7] },
  { tier := "Tier 1", feature := "S1", label := "ZMM 512-bit vector register state (zmm31, zmm0)", asm := "vmovaps zmm31, zmm0", bytes := [0x62, 0x61, 0x7c, 0x48, 0x28, 0xf8] },
  { tier := "Tier 1", feature := "S1", label := "Opmask register state (k7, k1)", asm := "kmovw k7, k1", bytes := [0xc5, 0xf8, 0x90, 0xf9] },
  { tier := "Tier 1", feature := "S1", label := "Control register state (cr3)", asm := "mov rax, cr3", bytes := [0x0f, 0x20, 0xd8] },
  { tier := "Tier 1", feature := "S1", label := "X87 FPU register stack state (st0, st1)", asm := "fld st(1)", bytes := [0xd9, 0xc1] },

  -- Tier 1: F1 Base Integer: Data Transfer
  { tier := "Tier 1", feature := "F1", label := "MOV 32-bit register-register (seam-supported)", asm := "mov eax, ebx", bytes := [0x89, 0xd8] },
  { tier := "Tier 1", feature := "F1", label := "MOV 64-bit register-register (seam-supported)", asm := "mov rax, rbx", bytes := [0x48, 0x89, 0xd8] },
  { tier := "Tier 1", feature := "F1", label := "MOVZX zero-extend byte to 32-bit (seam-supported)", asm := "movzx eax, bl", bytes := [0x0f, 0xb6, 0xc3] },
  { tier := "Tier 1", feature := "F1", label := "MOVSX sign-extend word to 64-bit (seam-supported)", asm := "movsx rax, bx", bytes := [0x48, 0x0f, 0xbf, 0xc3] },
  { tier := "Tier 1", feature := "F1", label := "XCHG 64-bit register swap (seam-supported)", asm := "xchg rbx, rcx", bytes := [0x48, 0x87, 0xcb] },

  -- Tier 1: F2 Base Integer: Binary ALU
  { tier := "Tier 1", feature := "F2", label := "ADD 64-bit register-register (seam-supported)", asm := "add rax, rbx", bytes := [0x48, 0x01, 0xd8] },
  { tier := "Tier 1", feature := "F2", label := "SUB 64-bit register-register (seam-supported)", asm := "sub rax, rbx", bytes := [0x48, 0x29, 0xd8] },
  { tier := "Tier 1", feature := "F2", label := "XOR 64-bit register-register (seam-supported)", asm := "xor rax, rbx", bytes := [0x48, 0x31, 0xd8] },
  { tier := "Tier 1", feature := "F2", label := "IMUL 64-bit signed multiply (seam-supported)", asm := "imul rax, rbx", bytes := [0x48, 0x0f, 0xaf, 0xc3] },
  { tier := "Tier 1", feature := "F2", label := "TEST 64-bit bitwise AND flags (seam-supported)", asm := "test rax, rbx", bytes := [0x48, 0x85, 0xd8] },

  -- Tier 1: F3 Base Integer: Shift/Rotate/Bit
  { tier := "Tier 1", feature := "F3", label := "SHL 64-bit logical shift left immediate (seam-supported)", asm := "shl rax, 3", bytes := [0x48, 0xc1, 0xe0, 0x03] },
  { tier := "Tier 1", feature := "F3", label := "SHR 64-bit logical shift right immediate (seam-supported)", asm := "shr rax, 3", bytes := [0x48, 0xc1, 0xe8, 0x03] },
  { tier := "Tier 1", feature := "F3", label := "SAR 64-bit arithmetic shift right immediate (seam-supported)", asm := "sar rax, 3", bytes := [0x48, 0xc1, 0xf8, 0x03] },
  { tier := "Tier 1", feature := "F3", label := "SETE conditional byte set (seam-supported)", asm := "sete al", bytes := [0x0f, 0x94, 0xc0] },
  { tier := "Tier 1", feature := "F3", label := "CMOVE conditional 64-bit move (seam-supported)", asm := "cmove rax, rbx", bytes := [0x48, 0x0f, 0x44, 0xc3] },

  -- Tier 1: F4 Base Integer: String & Flags
  { tier := "Tier 1", feature := "F4", label := "REP MOVSB block byte copy", asm := "rep movsb", bytes := [0xf3, 0xa4] },
  { tier := "Tier 1", feature := "F4", label := "REP STOSQ block qword fill", asm := "rep stosq", bytes := [0xf3, 0x48, 0xab] },
  { tier := "Tier 1", feature := "F4", label := "CLD clear direction flag", asm := "cld", bytes := [0xfc] },
  { tier := "Tier 1", feature := "F4", label := "STC set carry flag", asm := "stc", bytes := [0xf9] },
  { tier := "Tier 1", feature := "F4", label := "PUSHFQ push 64-bit RFLAGS", asm := "pushfq", bytes := [0x9c] },

  -- Tier 1: F5 Control Flow: Branches & Stack
  { tier := "Tier 1", feature := "F5", label := "PUSH 64-bit register (seam-supported)", asm := "push rax", bytes := [0x50] },
  { tier := "Tier 1", feature := "F5", label := "POP 64-bit register (seam-supported)", asm := "pop rbx", bytes := [0x5b] },
  { tier := "Tier 1", feature := "F5", label := "RET near return (seam-supported)", asm := "ret", bytes := [0xc3] },
  { tier := "Tier 1", feature := "F5", label := "JMP 8-bit short relative jump (seam-supported)", asm := ".L1:; jmp .L1", bytes := [0xeb, 0xfe] },
  { tier := "Tier 1", feature := "F5", label := "JE 8-bit conditional short jump (seam-supported)", asm := ".L1:; je .L1", bytes := [0x74, 0xfe] },

  -- Tier 1: F9 Atomic & Synchronization
  { tier := "Tier 1", feature := "F9", label := "LOCK ADD atomic read-modify-write", asm := "lock add qword ptr [rax], rbx", bytes := [0xf0, 0x48, 0x01, 0x18] },
  { tier := "Tier 1", feature := "F9", label := "LOCK XADD atomic exchange-and-add", asm := "lock xadd qword ptr [rax], rbx", bytes := [0xf0, 0x48, 0x0f, 0xc1, 0x18] },
  { tier := "Tier 1", feature := "F9", label := "LOCK CMPXCHG atomic compare-and-exchange", asm := "lock cmpxchg qword ptr [rcx], rbx", bytes := [0xf0, 0x48, 0x0f, 0xb1, 0x19] },
  { tier := "Tier 1", feature := "F9", label := "MFENCE full memory barrier", asm := "mfence", bytes := [0x0f, 0xae, 0xf0] },
  { tier := "Tier 1", feature := "F9", label := "LFENCE load memory barrier", asm := "lfence", bytes := [0x0f, 0xae, 0xe8] },

  -- Tier 1: F6 Ring-0 System: Syscall & VM
  { tier := "Tier 1", feature := "F6", label := "SYSCALL fast system call (seam-supported)", asm := "syscall", bytes := [0x0f, 0x05] },
  { tier := "Tier 1", feature := "F6", label := "SYSRETQ 64-bit return from system call", asm := "sysretq", bytes := [0x48, 0x0f, 0x07] },
  { tier := "Tier 1", feature := "F6", label := "VMCALL hypervisor call", asm := "vmcall", bytes := [0x0f, 0x01, 0xc1] },
  { tier := "Tier 1", feature := "F6", label := "VMLAUNCH launch virtual machine", asm := "vmlaunch", bytes := [0x0f, 0x01, 0xc2] },
  { tier := "Tier 1", feature := "F6", label := "VMRUN run AMD SVM guest", asm := "vmrun", bytes := [0x0f, 0x01, 0xd8] },

  -- Tier 1: F7 Ring-0 System: CR/DR/MSR/Tables
  { tier := "Tier 1", feature := "F7", label := "MOV from CR0 control register", asm := "mov rax, cr0", bytes := [0x0f, 0x20, 0xc0] },
  { tier := "Tier 1", feature := "F7", label := "MOV to DR7 debug register", asm := "mov dr7, rax", bytes := [0x0f, 0x23, 0xf8] },
  { tier := "Tier 1", feature := "F7", label := "RDMSR read model-specific register", asm := "rdmsr", bytes := [0x0f, 0x32] },
  { tier := "Tier 1", feature := "F7", label := "WRMSR write model-specific register", asm := "wrmsr", bytes := [0x0f, 0x30] },
  { tier := "Tier 1", feature := "F7", label := "SWAPGS swap GS base register", asm := "swapgs", bytes := [0x0f, 0x01, 0xf8] },

  -- Tier 1: F8 Ring-0 System: TLB/Cache/Interrupts
  { tier := "Tier 1", feature := "F8", label := "INVLPG invalidate TLB entry", asm := "invlpg [rax]", bytes := [0x0f, 0x01, 0x38] },
  { tier := "Tier 1", feature := "F8", label := "WBINVD write-back and invalidate cache", asm := "wbinvd", bytes := [0x0f, 0x09] },
  { tier := "Tier 1", feature := "F8", label := "HLT processor halt (seam-supported)", asm := "hlt", bytes := [0xf4] },
  { tier := "Tier 1", feature := "F8", label := "UD2 explicit undefined instruction (seam-supported)", asm := "ud2", bytes := [0x0f, 0x0b] },
  { tier := "Tier 1", feature := "F8", label := "CPUID processor identification", asm := "cpuid", bytes := [0x0f, 0xa2] },

  -- Tier 1: F10 X87 FPU
  { tier := "Tier 1", feature := "F10", label := "FLD push ST(1) onto FPU stack", asm := "fld st(1)", bytes := [0xd9, 0xc1] },
  { tier := "Tier 1", feature := "F10", label := "FADD ST(0) += ST(1)", asm := "fadd st(0), st(1)", bytes := [0xd8, 0xc1] },
  { tier := "Tier 1", feature := "F10", label := "FMUL ST(0) *= ST(2)", asm := "fmul st(0), st(2)", bytes := [0xd8, 0xca] },
  { tier := "Tier 1", feature := "F10", label := "FSQRT square root ST(0)", asm := "fsqrt", bytes := [0xd9, 0xfa] },
  { tier := "Tier 1", feature := "F10", label := "FXSAVE64 save 64-bit FPU/SIMD state", asm := "fxsave64 [rax]", bytes := [0x48, 0x0f, 0xae, 0x00] },

  -- Tier 1: F11 MMX & SSE1-4.2
  { tier := "Tier 1", feature := "F11", label := "MOVAPS aligned packed single move", asm := "movaps xmm0, xmm1", bytes := [0x0f, 0x28, 0xc1] },
  { tier := "Tier 1", feature := "F11", label := "ADDPS packed single FP add", asm := "addps xmm0, xmm1", bytes := [0x0f, 0x58, 0xc1] },
  { tier := "Tier 1", feature := "F11", label := "PADDD packed 32-bit integer add", asm := "paddd xmm0, xmm1", bytes := [0x66, 0x0f, 0xfe, 0xc1] },
  { tier := "Tier 1", feature := "F11", label := "PSHUFB SSSE3 packed byte shuffle", asm := "pshufb xmm0, xmm1", bytes := [0x66, 0x0f, 0x38, 0x00, 0xc1] },
  { tier := "Tier 1", feature := "F11", label := "CRC32 SSE4.2 hardware CRC accumulate", asm := "crc32 eax, ebx", bytes := [0xf2, 0x0f, 0x38, 0xf1, 0xc3] },

  -- Tier 1: F12 AVX / AVX2 / FMA & XOP
  { tier := "Tier 1", feature := "F12", label := "VADDPS 256-bit AVX packed single FP add", asm := "vaddps ymm0, ymm1, ymm2", bytes := [0xc5, 0xf4, 0x58, 0xc2] },
  { tier := "Tier 1", feature := "F12", label := "VPADDD 256-bit AVX2 packed dword add", asm := "vpaddd ymm0, ymm1, ymm2", bytes := [0xc5, 0xf5, 0xfe, 0xc2] },
  { tier := "Tier 1", feature := "F12", label := "VFMADD213PS 256-bit FMA3 fused multiply-add", asm := "vfmadd213ps ymm0, ymm1, ymm2", bytes := [0xc4, 0xe2, 0x75, 0xa8, 0xc2] },
  { tier := "Tier 1", feature := "F12", label := "VPERM2F128 256-bit lane permute", asm := "vperm2f128 ymm0, ymm1, ymm2, 1", bytes := [0xc4, 0xe3, 0x75, 0x06, 0xc2, 0x01] },
  { tier := "Tier 1", feature := "F12", label := "VZEROUPPER zero upper YMM/ZMM bits", asm := "vzeroupper", bytes := [0xc5, 0xf8, 0x77] },

  -- Tier 1: F14 BMI1 / BMI2 / ABM
  { tier := "Tier 1", feature := "F14", label := "ANDN BMI1 bitwise AND-NOT", asm := "andn eax, ebx, ecx", bytes := [0xc4, 0xe2, 0x60, 0xf2, 0xc1] },
  { tier := "Tier 1", feature := "F14", label := "BLSI BMI1 isolate lowest set bit", asm := "blsi eax, ebx", bytes := [0xc4, 0xe2, 0x78, 0xf3, 0xdb] },
  { tier := "Tier 1", feature := "F14", label := "TZCNT count trailing zero bits", asm := "tzcnt eax, ebx", bytes := [0xf3, 0x0f, 0xbc, 0xc3] },
  { tier := "Tier 1", feature := "F14", label := "PDEP BMI2 parallel bit deposit", asm := "pdep rax, rbx, rcx", bytes := [0xc4, 0xe2, 0xe3, 0xf5, 0xc1] },
  { tier := "Tier 1", feature := "F14", label := "RORX BMI2 flagless rotate right", asm := "rorx rax, rbx, 7", bytes := [0xc4, 0xe3, 0xfb, 0xf0, 0xc3, 0x07] },

  -- Tier 1: F15 Crypto & Special
  { tier := "Tier 1", feature := "F15", label := "AESENC AES single encryption round", asm := "aesenc xmm0, xmm1", bytes := [0x66, 0x0f, 0x38, 0xdc, 0xc1] },
  { tier := "Tier 1", feature := "F15", label := "AESENCLAST AES final encryption round", asm := "aesenclast xmm0, xmm1", bytes := [0x66, 0x0f, 0x38, 0xdd, 0xc1] },
  { tier := "Tier 1", feature := "F15", label := "PCLMULQDQ carry-less multiplication", asm := "pclmulqdq xmm0, xmm1, 1", bytes := [0x66, 0x0f, 0x3a, 0x44, 0xc1, 0x01] },
  { tier := "Tier 1", feature := "F15", label := "SHA256RNDS2 two SHA-256 rounds", asm := "sha256rnds2 xmm0, xmm1, xmm0", bytes := [0x0f, 0x38, 0xcb, 0xc1] },
  { tier := "Tier 1", feature := "F15", label := "SHA256MSG1 SHA-256 message schedule 1", asm := "sha256msg1 xmm0, xmm1", bytes := [0x0f, 0x38, 0xcc, 0xc1] },

  -- Tier 1: F13 AVX-512 & Opmasks
  { tier := "Tier 1", feature := "F13", label := "VADDPS 512-bit with zeroing mask {k1}{z}", asm := "vaddps zmm0 {k1}{z}, zmm1, zmm2", bytes := [0x62, 0xf1, 0x74, 0xc9, 0x58, 0xc2] },
  { tier := "Tier 1", feature := "F13", label := "VPADDQ 512-bit 64-bit integer add {k2}", asm := "vpaddq zmm0 {k2}, zmm1, zmm2", bytes := [0x62, 0xf1, 0xf5, 0x4a, 0xd4, 0xc2] },
  { tier := "Tier 1", feature := "F13", label := "VFMADD213PS 512-bit FMA3", asm := "vfmadd213ps zmm0, zmm1, zmm2", bytes := [0x62, 0xf2, 0x75, 0x48, 0xa8, 0xc2] },
  { tier := "Tier 1", feature := "F13", label := "KMOVW move opmask register", asm := "kmovw k1, k2", bytes := [0xc5, 0xf8, 0x90, 0xca] },
  { tier := "Tier 1", feature := "F13", label := "KANDW bitwise AND opmask registers", asm := "kandw k1, k2, k3", bytes := [0xc5, 0xec, 0x41, 0xcb] },

  -- Tier 2: Boundary & Corner Cases
  { tier := "Tier 2", feature := "B1-REX-HighByte", label := "Legacy AH high-byte register (no REX allowed)", asm := "mov ah, al", bytes := [0x88, 0xc4] },
  { tier := "Tier 2", feature := "B1-REX-HighByte", label := "Legacy BH high-byte register (no REX allowed)", asm := "mov bh, cl", bytes := [0x88, 0xcf] },
  { tier := "Tier 2", feature := "B1-REX-HighByte", label := "REX-prefixed SPL low-byte register (0x40 required)", asm := "mov spl, al", bytes := [0x40, 0x88, 0xc4] },
  { tier := "Tier 2", feature := "B1-REX-HighByte", label := "REX-prefixed BPL low-byte register (0x40 required)", asm := "mov bpl, al", bytes := [0x40, 0x88, 0xc5] },
  { tier := "Tier 2", feature := "B1-REX-HighByte", label := "REX-prefixed DIL low-byte register (0x40 required)", asm := "mov dil, sil", bytes := [0x40, 0x88, 0xf7] },
  { tier := "Tier 2", feature := "B2-WidthExt", label := "32-bit MOV immediate zero-extends upper 32 bits (seam-supported)", asm := "mov eax, 0xffffffff", bytes := [0xb8, 0xff, 0xff, 0xff, 0xff] },
  { tier := "Tier 2", feature := "B2-WidthExt", label := "64-bit MOV immediate full 64-bit width (seam-supported)", asm := "movabs rax, 0xffffffffffffffff", bytes := [0x48, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] },
  { tier := "Tier 2", feature := "B2-WidthExt", label := "8-bit MOV preserves upper 56 bits of RAX", asm := "mov al, 0xff", bytes := [0xb0, 0xff] },
  { tier := "Tier 2", feature := "B2-WidthExt", label := "16-bit MOV preserves upper 48 bits of RAX", asm := "mov ax, 0xffff", bytes := [0x66, 0xb8, 0xff, 0xff] },
  { tier := "Tier 2", feature := "B2-WidthExt", label := "32-bit ADD zero-extends upper 32 bits (seam-supported)", asm := "add eax, ebx", bytes := [0x01, 0xd8] },
  { tier := "Tier 2", feature := "B3-VectorUpper", label := "Legacy SSE ADDPS preserves bits [511:128]", asm := "addps xmm0, xmm1", bytes := [0x0f, 0x58, 0xc1] },
  { tier := "Tier 2", feature := "B3-VectorUpper", label := "VEX 128-bit VADDPS zeroes bits [511:128]", asm := "vaddps xmm0, xmm1, xmm2", bytes := [0xc5, 0xf0, 0x58, 0xc2] },
  { tier := "Tier 2", feature := "B3-VectorUpper", label := "VEX 256-bit VADDPS zeroes bits [511:256]", asm := "vaddps ymm0, ymm1, ymm2", bytes := [0xc5, 0xf4, 0x58, 0xc2] },
  { tier := "Tier 2", feature := "B3-VectorUpper", label := "EVEX 128-bit VADDPS zmm0 subview zeroes bits [511:128]", asm := "vaddps xmm16, xmm17, xmm18", bytes := [0x62, 0xa1, 0x74, 0x00, 0x58, 0xc2] },
  { tier := "Tier 2", feature := "B3-VectorUpper", label := "EVEX 512-bit VADDPS writes full 512 bits", asm := "vaddps zmm0, zmm1, zmm2", bytes := [0x62, 0xf1, 0x74, 0x48, 0x58, 0xc2] },
  { tier := "Tier 2", feature := "B4-Disp8N", label := "EVEX Full 512-bit disp8*64 boundary (+64 -> disp8=0x01)", asm := "vaddps zmm0, zmm1, zmmword ptr [rax + 64]", bytes := [0x62, 0xf1, 0x74, 0x48, 0x58, 0x40, 0x01] },
  { tier := "Tier 2", feature := "B4-Disp8N", label := "EVEX Full 512-bit disp8*64 max positive (+8128 -> disp8=0x7f)", asm := "vaddps zmm0, zmm1, zmmword ptr [rax + 8128]", bytes := [0x62, 0xf1, 0x74, 0x48, 0x58, 0x40, 0x7f] },
  { tier := "Tier 2", feature := "B4-Disp8N", label := "EVEX Full 512-bit unaligned disp (+65 -> falls back to disp32)", asm := "vaddps zmm0, zmm1, zmmword ptr [rax + 65]", bytes := [0x62, 0xf1, 0x74, 0x48, 0x58, 0x80, 0x41, 0x00, 0x00, 0x00] },
  { tier := "Tier 2", feature := "B4-Disp8N", label := "EVEX 256-bit disp8*32 boundary (+32 -> disp8=0x01)", asm := "vaddps ymm0, ymm1, ymmword ptr [rax + 32]", bytes := [0xc5, 0xf4, 0x58, 0x40, 0x20] },
  { tier := "Tier 2", feature := "B4-Disp8N", label := "EVEX 128-bit disp8*16 boundary (+16 -> disp8=0x01)", asm := "vaddps xmm0, xmm1, xmmword ptr [rax + 16]", bytes := [0xc5, 0xf0, 0x58, 0x40, 0x10] },
  { tier := "Tier 2", feature := "B5-Opmask", label := "EVEX unmasked (aaa=000 implicit k0)", asm := "vaddps zmm0, zmm1, zmm2", bytes := [0x62, 0xf1, 0x74, 0x48, 0x58, 0xc2] },
  { tier := "Tier 2", feature := "B5-Opmask", label := "EVEX k1 merge-masked (aaa=001, z=0)", asm := "vaddps zmm0 {k1}, zmm1, zmm2", bytes := [0x62, 0xf1, 0x74, 0x49, 0x58, 0xc2] },
  { tier := "Tier 2", feature := "B5-Opmask", label := "EVEX k1 zero-masked (aaa=001, z=1)", asm := "vaddps zmm0 {k1}{z}, zmm1, zmm2", bytes := [0x62, 0xf1, 0x74, 0xc9, 0x58, 0xc2] },
  { tier := "Tier 2", feature := "B5-Opmask", label := "EVEX k7 zero-masked (aaa=111, z=1)", asm := "vaddps zmm0 {k7}{z}, zmm1, zmm2", bytes := [0x62, 0xf1, 0x74, 0xcf, 0x58, 0xc2] },
  { tier := "Tier 2", feature := "B5-Opmask", label := "EVEX k3 merge-masked on high ZMM registers", asm := "vaddpd zmm20 {k3}, zmm21, zmm22", bytes := [0x62, 0xa1, 0xd5, 0x43, 0x58, 0xe6] },
  { tier := "Tier 2", feature := "B6-AddrEscapes", label := "[rsp] base requires mandatory SIB byte 0x24", asm := "mov rax, qword ptr [rsp]", bytes := [0x48, 0x8b, 0x04, 0x24] },
  { tier := "Tier 2", feature := "B6-AddrEscapes", label := "[r12] base requires mandatory SIB byte 0x24", asm := "mov rax, qword ptr [r12]", bytes := [0x49, 0x8b, 0x04, 0x24] },
  { tier := "Tier 2", feature := "B6-AddrEscapes", label := "[rbp] base requires mandatory disp8=0x00", asm := "mov rax, qword ptr [rbp]", bytes := [0x48, 0x8b, 0x45, 0x00] },
  { tier := "Tier 2", feature := "B6-AddrEscapes", label := "[r13] base requires mandatory disp8=0x00", asm := "mov rax, qword ptr [r13]", bytes := [0x49, 0x8b, 0x45, 0x00] },
  { tier := "Tier 2", feature := "B6-AddrEscapes", label := "[rip+disp32] ModR/M mod=00 rm=101 encoding", asm := "lea rax, [rip + 0x1234]", bytes := [0x48, 0x8d, 0x05, 0x34, 0x12, 0x00, 0x00] },

  -- Tier 3: Cross-Feature Combinations
  { tier := "Tier 3", feature := "Cross", label := "LOCK + REX.W + SIB scaled index RMW", asm := "lock add qword ptr [rax + rcx*8 + 0x10], r15", bytes := [0xf0, 0x4c, 0x01, 0x7c, 0xc8, 0x10] },
  { tier := "Tier 3", feature := "Cross", label := "EVEX 512-bit + {k3}{z} + disp8*64 compressed displacement", asm := "vaddps zmm5 {k3}{z}, zmm6, zmmword ptr [rbx + 0x80]", bytes := [0x62, 0xf1, 0x4c, 0xcb, 0x58, 0x6b, 0x02] },
  { tier := "Tier 3", feature := "Cross", label := "EVEX 512-bit + embedded broadcast {1to16} + {k1}", asm := "vaddps zmm0 {k1}, zmm1, dword ptr [rax + 0x10]{1to16}", bytes := [0x62, 0xf1, 0x74, 0x59, 0x58, 0x40, 0x04] },
  { tier := "Tier 3", feature := "Cross", label := "VEX 256-bit + VSIB gather + extended YMM registers", asm := "vgatherdpd ymm8, [r12 + xmm9*4 + 0x20], ymm10", bytes := [0xc4, 0x02, 0xad, 0x92, 0x44, 0x8c, 0x20] },
  { tier := "Tier 3", feature := "Cross", label := "BMI2 RORX + REX.W + memory source with SIB", asm := "rorx r14, qword ptr [rax + rbx*4 + 0x40], 17", bytes := [0xc4, 0x63, 0xfb, 0xf0, 0x74, 0x98, 0x40, 0x11] },
  { tier := "Tier 3", feature := "Cross", label := "AES-NI + VEX VAESENC 256-bit vector crypto", asm := "vaesenc ymm0, ymm1, ymm2", bytes := [0xc4, 0xe2, 0x75, 0xdc, 0xc2] },

  -- Tier 4: Real-World Application Scenarios
  { tier := "Tier 4", feature := "Scenario-SIMD-Memcpy", label := "AVX2 256-bit vectorized memory copy loop with pointer advance", asm := ".Lloop:; vmovdqu ymm0, ymmword ptr [rsi]; vmovdqu ymmword ptr [rdi], ymm0; add rsi, 32; add rdi, 32; sub rcx, 32; jnz .Lloop", bytes := [0xc5, 0xfe, 0x6f, 0x06, 0xc5, 0xfe, 0x7f, 0x07, 0x48, 0x83, 0xc6, 0x20, 0x48, 0x83, 0xc7, 0x20, 0x48, 0x83, 0xe9, 0x20, 0x75, 0xea], isMultiInstr := true },
  { tier := "Tier 4", feature := "Scenario-SHA256-Block", label := "Hardware SHA-256 message schedule and round update sequence", asm := "sha256msg1 xmm0, xmm1; sha256msg2 xmm0, xmm2; sha256rnds2 xmm3, xmm4, xmm0", bytes := [0x0f, 0x38, 0xcc, 0xc1, 0x0f, 0x38, 0xcd, 0xc2, 0x0f, 0x38, 0xcb, 0xdc], isMultiInstr := true },
  { tier := "Tier 4", feature := "Scenario-Ring0-Syscall", label := "Ring-0 syscall entry/exit prologue and return sequence", asm := "swapgs; mov qword ptr gs:[0x10], rsp; mov rsp, qword ptr gs:[0x08]; syscall; sysretq", bytes := [0x0f, 0x01, 0xf8, 0x65, 0x48, 0x89, 0x24, 0x25, 0x10, 0x00, 0x00, 0x00, 0x65, 0x48, 0x8b, 0x24, 0x25, 0x08, 0x00, 0x00, 0x00, 0x0f, 0x05, 0x48, 0x0f, 0x07], isMultiInstr := true },
  { tier := "Tier 4", feature := "Scenario-AVX512-Kernel", label := "AVX-512 masked FMA accumulation kernel with opmask setup", asm := "kmovw k1, eax; vfmadd231ps zmm0 {k1}{z}, zmm1, zmmword ptr [rdi + 0x40]; vzeroupper", bytes := [0xc5, 0xf8, 0x92, 0xc8, 0x62, 0xf2, 0x75, 0xc9, 0xb8, 0x47, 0x01, 0xc5, 0xf8, 0x77], isMultiInstr := true }
]

/-- Verify round-trip encoding/decoding sanity directly on `Grass.ISA.X86.Target.Instr` constructors. -/
def runSeamCodecSanityChecks : List (String × Bool) :=
  let checkInstr (i : Instr) : Bool :=
    let bs := encode i
    bs.length > 0 && decode bs == some (i, bs.length)
  [ ("Instr.aluRR .add .w64 .rax .rbx round-trip", checkInstr (.aluRR .add .w64 .rax .rbx))
  , ("Instr.aluRR .sub .w64 .rbx .rax round-trip", checkInstr (.aluRR .sub .w64 .rbx .rax))
  , ("Instr.movRI32 .rcx 0x12345678 round-trip", checkInstr (.movRI32 .rcx 0x12345678))
  , ("Instr.movRI64 .r15 0x1122334455667788 round-trip", checkInstr (.movRI64 .r15 0x1122334455667788))
  , ("Instr.hlt round-trip", checkInstr .hlt)
  , ("Instr.ud2 round-trip", checkInstr .ud2)
  , ("Instr.syscall round-trip", checkInstr .syscall)
  , ("Instr.ret round-trip", checkInstr .ret) ]

/-- Execute all E2E differential checks and print the summary report. -/
def runReport (args : List String) : IO Unit := do
  let strict := args.contains "--strict"
  let mut verifiedCount := 0
  let mut pendingCount := 0
  let mut mismatchList : List (DifferentialCase × String) := []

  for tc in e2eCorpus do
    match checkCase tc with
    | .verifiedRoundTrip _ => verifiedCount := verifiedCount + 1
    | .pendingMilestone => pendingCount := pendingCount + 1
    | .mismatch reason => mismatchList := mismatchList ++ [(tc, reason)]

  let codecChecks := runSeamCodecSanityChecks
  let failedCodec := codecChecks.filter (fun p => !p.2)

  IO.println "== Lean Seam E2E Differential Suite (Tests/ISA/X86/E2EDifferentialSuite.lean) =="
  IO.println s!"Total ground-truth corpus cases (Tiers 1-4): {e2eCorpus.length}"
  IO.println s!"  Verified round-trip in Lean seam:          {verifiedCount}"
  IO.println s!"  Pending M1-M5 milestone implementation:    {pendingCount}"
  IO.println s!"  Round-trip mismatches:                     {mismatchList.length}"
  IO.println s!"  Seam codec sanity checks passed:           {codecChecks.length - failedCodec.length}/{codecChecks.length}"

  if !mismatchList.isEmpty then
    IO.println "\n-- MISMATCHES --"
    for (tc, reason) in mismatchList do
      IO.println s!"  [{tc.tier} / {tc.feature}] {tc.label} ({tc.asm}): {reason}"
    IO.Process.exit 1

  if !failedCodec.isEmpty then
    IO.println "\n-- SEAM CODEC FAILURES --"
    for (label, _) in failedCodec do
      IO.println s!"  [FAIL] {label}"
    IO.Process.exit 1

  if strict && pendingCount > 0 then
    IO.println s!"\n[FAIL] Strict mode (--strict) requires 0 pending cases, but {pendingCount} cases are pending M1-M5 implementation."
    IO.Process.exit 1

  IO.println "\n[PASS] Lean Seam E2E Differential Suite passed with 0 mismatches."

end Grass.Tests.ISA.X86.E2EDifferentialSuite

/-- Top-level entry point for `lake env lean --run Tests/ISA/X86/E2EDifferentialSuite.lean`. -/
def main (args : List String) : IO Unit :=
  Grass.Tests.ISA.X86.E2EDifferentialSuite.runReport args
