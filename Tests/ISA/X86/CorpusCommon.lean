import Grass.ISA.X86.Bytes

/-!
# Shared corpus helpers

Formatting and constants used by both differential corpora:
`Tests/ISA/X86/NasmCorpus.lean` (assembler agreement) and
`Tests/ISA/X86/RipCorpus.lean` (disassembler agreement on the RIP-relative
form). Each of those defines its own `main`, so the shared parts live here
rather than in one of them.

## Why the displacement is `0x11223344`

Four distinct non-zero bytes, so a byte-order error is visible rather than
palindromic, and too large for a signed 8-bit displacement — which matters
because Grass's encoder always emits `disp32` while NASM emits the shortest
form. With a displacement NASM cannot shorten, the two agree exactly and a byte
comparison is meaningful. A displacement of `8` would make NASM choose `disp8`
and produce a legitimately different, shorter encoding; that is a real
difference in policy, not a defect, and it is excluded here rather than papered
over.
-/

namespace Grass.Tests.ISA.X86.Corpus

open Grass.Std.Logical Grass.ISA.X86

/-- The displacement used throughout both corpora. -/
def disp : BitVec 32 := 0x11223344

/-- The immediate used by the `mov` cases. -/
def immValue : BitVec 32 := 0x55667788

/-- NASM's 64-bit name for a register. -/
def nasmName : Gpr -> String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- The assembler's spelling of an XMM register. -/
def xmmName : Xmm -> String
  | .xmm0 => "xmm0" | .xmm1 => "xmm1" | .xmm2 => "xmm2" | .xmm3 => "xmm3"
  | .xmm4 => "xmm4" | .xmm5 => "xmm5" | .xmm6 => "xmm6" | .xmm7 => "xmm7"
  | .xmm8 => "xmm8" | .xmm9 => "xmm9" | .xmm10 => "xmm10" | .xmm11 => "xmm11"
  | .xmm12 => "xmm12" | .xmm13 => "xmm13" | .xmm14 => "xmm14"
  | .xmm15 => "xmm15"

/-- The 32-bit name of a register, for probe labels and disassembly text. -/
def nasmName32 : Gpr -> String
  | .rax => "eax" | .rcx => "ecx" | .rdx => "edx" | .rbx => "ebx"
  | .rsp => "esp" | .rbp => "ebp" | .rsi => "esi" | .rdi => "edi"
  | .r8 => "r8d" | .r9 => "r9d" | .r10 => "r10d" | .r11 => "r11d"
  | .r12 => "r12d" | .r13 => "r13d" | .r14 => "r14d" | .r15 => "r15d"

/-- NASM's spelling of a scale factor. -/
def scaleText : Scale -> String
  | .s1 => "1" | .s2 => "2" | .s4 => "4" | .s8 => "8"

/-- Lowercase hex for one byte, zero-padded to two digits. -/
def hexByte (b : Byte) : String :=
  let digits : List Char :=
    ['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let n := b.toNat
  String.ofList [digits.getD (n / 16) '?', digits.getD (n % 16) '?']

/-- Lowercase hex for a byte string, no separators. -/
def hexBytes (bs : ByteSeq) : String := String.join (bs.map hexByte)

/-- A 64-bit value in lowercase hex with no leading zeros, which is how NDISASM
prints a RIP-relative target. `0` prints as `0`, not as the empty string. -/
def hexTrim (v : BitVec 64) : String :=
  let full := hexBytes
    [BitVec.extractLsb' 56 8 v, BitVec.extractLsb' 48 8 v,
     BitVec.extractLsb' 40 8 v, BitVec.extractLsb' 32 8 v,
     BitVec.extractLsb' 24 8 v, BitVec.extractLsb' 16 8 v,
     BitVec.extractLsb' 8 8 v, BitVec.extractLsb' 0 8 v]
  -- `String.dropWhile` returns a slice in this toolchain, so take the list
  -- route: it is a sixteen-character string and clarity beats cleverness.
  let trimmed := String.ofList (full.toList.dropWhile (· == '0'))
  if trimmed.isEmpty then "0" else trimmed

/-- A 32-bit value as a NASM hex literal. -/
def hex32 (v : BitVec 32) : String :=
  "0x" ++ hexBytes [BitVec.extractLsb' 24 8 v, BitVec.extractLsb' 16 8 v,
                    BitVec.extractLsb' 8 8 v, BitVec.extractLsb' 0 8 v]

/-- A 64-bit value as a NASM hex literal, zero-padded to sixteen digits.

Padded rather than trimmed because NASM sizes an unadorned literal by its
written width in some contexts; a full-width literal is unambiguous. -/
def hex64 (v : BitVec 64) : String :=
  "0x" ++ hexBytes
    [BitVec.extractLsb' 56 8 v, BitVec.extractLsb' 48 8 v,
     BitVec.extractLsb' 40 8 v, BitVec.extractLsb' 32 8 v,
     BitVec.extractLsb' 24 8 v, BitVec.extractLsb' 16 8 v,
     BitVec.extractLsb' 8 8 v, BitVec.extractLsb' 0 8 v]

end Grass.Tests.ISA.X86.Corpus
