import Grass.ISA.X86.Target.Encode

/-!
# Canonical encoded lengths for `Grass.ISA.X86.Target.Instr`

`Grass/Assembly/Lower/X86.lean`'s `lower_size` obligation needs, for every
`Instr` constructor it can emit, the length of `Grass.ISA.X86.Target.encode`
applied to it. `Grass/ISA/X86/Target/Encode.lean` proves the encode/decode
round trip family by family but states no length lemma of its own (its only
length fact is `encode_pos`, "at least one byte"); this file adds the missing
half, as its own module rather than an edit to `Encode.lean`.

Every length below is a closed formula in the instruction's own fields (an
`if` over whether a REX prefix is forced, plus the fixed opcode/immediate
byte counts `encodeCore` already fixes) rather than a case split over all
sixteen registers: `maybeRex_length` reduces the only register-dependent
part — whether the REX byte is present at all — to the same three flags
`encodeCore` computes it from, so each instruction's proof is one `simp`
unfolding `encode`/`encodeCore` against that one lemma, not sixteen (or, for
two-register forms, 256) closed instances.
-/

namespace Grass.ISA.X86.Target

open Grass.Std.Logical (Byte ByteSeq)

/-- `maybeRex`'s length: one byte exactly when some flag forces the prefix,
none otherwise. The single fact every length lemma below reduces to. -/
@[simp] theorem maybeRex_length (w a b c : Bool) :
    (maybeRex w a b c).length = if w || a || b || c then 1 else 0 := by
  unfold maybeRex
  split <;> simp

/-- `encode` factors through `encodeCore` by a length-preserving `map`. -/
theorem encode_length_eq (instr : Instr) : (encode instr).length = (encodeCore instr).length := by
  simp [encode]

theorem encode_length_movRR (sz : Sz) (dst src : Gpr) :
    (encode (.movRR sz dst src)).length =
      (if sz.isW64 || src.isExtended || dst.isExtended then 1 else 0) + 2 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_movRI32 (dst : Gpr) (imm : BitVec 32) :
    (encode (.movRI32 dst imm)).length = (if dst.isExtended then 1 else 0) + 5 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_movRI64 (dst : Gpr) (imm : BitVec 64) :
    (encode (.movRI64 dst imm)).length = 10 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_movzxRR (dstSz : Sz) (dst src : Gpr) (srcIs16 : Bool) :
    (encode (.movzxRR dstSz dst src srcIs16)).length =
      (if dstSz.isW64 || dst.isExtended || src.isExtended then 1 else 0) + 3 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_movsxRR (dstSz : Sz) (dst src : Gpr) (srcIs16 : Bool) :
    (encode (.movsxRR dstSz dst src srcIs16)).length =
      (if dstSz.isW64 || dst.isExtended || src.isExtended then 1 else 0) + 3 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_aluRR (op : AluOp) (sz : Sz) (dst src : Gpr) :
    (encode (.aluRR op sz dst src)).length =
      (if sz.isW64 || src.isExtended || dst.isExtended then 1 else 0) + 2 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_aluRI (op : AluOp) (sz : Sz) (dst : Gpr) (imm : BitVec 32) :
    (encode (.aluRI op sz dst imm)).length =
      (if sz.isW64 || dst.isExtended then 1 else 0) + 6 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_testRR (sz : Sz) (a b : Gpr) :
    (encode (.testRR sz a b)).length =
      (if sz.isW64 || b.isExtended || a.isExtended then 1 else 0) + 2 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_testRI (sz : Sz) (a : Gpr) (imm : BitVec 32) :
    (encode (.testRI sz a imm)).length =
      (if sz.isW64 || a.isExtended then 1 else 0) + 6 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_shiftImm (op : ShiftOp) (sz : Sz) (dst : Gpr) (imm : BitVec 8) :
    (encode (.shiftImm op sz dst imm)).length =
      (if sz.isW64 || dst.isExtended then 1 else 0) + 3 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_imul2 (sz : Sz) (dst src : Gpr) :
    (encode (.imul2 sz dst src)).length =
      (if sz.isW64 || dst.isExtended || src.isExtended then 1 else 0) + 3 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_inc (sz : Sz) (dst : Gpr) :
    (encode (.inc sz dst)).length = (if sz.isW64 || dst.isExtended then 1 else 0) + 2 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_dec (sz : Sz) (dst : Gpr) :
    (encode (.dec sz dst)).length = (if sz.isW64 || dst.isExtended then 1 else 0) + 2 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_push (r : Gpr) :
    (encode (.push r)).length = (if r.isExtended then 1 else 0) + 1 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_pop (r : Gpr) :
    (encode (.pop r)).length = (if r.isExtended then 1 else 0) + 1 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_callRel32 (rel : BitVec 32) : (encode (.callRel32 rel)).length = 5 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_ret : (encode .ret).length = 1 := by simp [encode_length_eq, encodeCore]

theorem encode_length_jmpRel32 (rel : BitVec 32) : (encode (.jmpRel32 rel)).length = 5 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_jmpRel8 (rel : BitVec 8) : (encode (.jmpRel8 rel)).length = 2 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_jccRel32 (cc : Cond) (rel : BitVec 32) :
    (encode (.jccRel32 cc rel)).length = 6 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_jccRel8 (cc : Cond) (rel : BitVec 8) :
    (encode (.jccRel8 cc rel)).length = 2 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_syscall : (encode .syscall).length = 2 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_ud2 : (encode .ud2).length = 2 := by simp [encode_length_eq, encodeCore]

theorem encode_length_hlt : (encode .hlt).length = 1 := by simp [encode_length_eq, encodeCore]

theorem encode_length_nop : (encode .nop).length = 1 := by simp [encode_length_eq, encodeCore]

theorem encode_length_cdq : (encode .cdq).length = 1 := by simp [encode_length_eq, encodeCore]

theorem encode_length_cqo : (encode .cqo).length = 2 := by simp [encode_length_eq, encodeCore]

theorem encode_length_div (sz : Sz) (src : Gpr) :
    (encode (.div sz src)).length = (if sz.isW64 || src.isExtended then 1 else 0) + 2 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_idiv (sz : Sz) (src : Gpr) :
    (encode (.idiv sz src)).length = (if sz.isW64 || src.isExtended then 1 else 0) + 2 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_mul (sz : Sz) (src : Gpr) :
    (encode (.mul sz src)).length = (if sz.isW64 || src.isExtended then 1 else 0) + 2 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_setcc (cc : Cond) (dst : Gpr) :
    (encode (.setcc cc dst)).length = (if dst.isExtended then 1 else 0) + 3 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_cmovcc (sz : Sz) (cc : Cond) (dst src : Gpr) :
    (encode (.cmovcc sz cc dst src)).length =
      (if sz.isW64 || dst.isExtended || src.isExtended then 1 else 0) + 3 := by
  simp [encode_length_eq, encodeCore]

theorem encode_length_xchgRR (sz : Sz) (a b : Gpr) :
    (encode (.xchgRR sz a b)).length =
      (if sz.isW64 || b.isExtended || a.isExtended then 1 else 0) + 2 := by
  simp [encode_length_eq, encodeCore]

end Grass.ISA.X86.Target
