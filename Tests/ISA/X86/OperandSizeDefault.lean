import Grass.ISA.X86.Bytes

/-!
# Which instructions default to a 64-bit operand size

`Grass.ISA.X86.Width.default64BitMode` records that 64-bit mode defaults to
32-bit operands, and its docstring recorded that two groups of instructions do
not follow the rule -- near branches, and everything except far branches that
implicitly references RSP -- with the model owed rather than built.
`operandSizeDefault?` is that model. These pin what it answers.

The `FF` rows are the reason it takes a `/digit`. One opcode byte carries a near
call, a far call, a near jump, a far jump, `push r/m`, `inc` and `dec`, and the
manual's sentence puts them in three different places.
-/

namespace Tests.ISA.X86.OperandSizeDefault

open Grass.ISA.X86

/-! ## The second group -/

/-- `push r64` references RSP implicitly. -/
example : operandSizeDefault? false 0x50 none = some .sixtyFour := rfl
/-- and so does `pop r64`. -/
example : operandSizeDefault? false 0x5F none = some .sixtyFour := rfl
/-- `jmp rel32` is a near branch. -/
example : operandSizeDefault? false 0xE9 none = some .sixtyFour := rfl
/-- `jz rel32` in the two-byte space is one too. -/
example : operandSizeDefault? true 0x84 none = some .sixtyFour := rfl
/-- `ret`. -/
example : operandSizeDefault? false 0xC3 none = some .sixtyFour := rfl

/-! ## `FF`, where the digit decides

Three answers from one opcode byte. A model indexed on the byte alone has to be
wrong about at least two of these. -/

/-- `/2` is a near call: first group. This is why
`Grass.ISA.X86.callMem64` sets `w := false` -- the docstring there says the
`REX.W` is neither needed nor permitted, and this is the fact behind it. -/
example : operandSizeDefault? false 0xFF (some 2) = some .sixtyFour := rfl

/-- `/4` is a near jump: first group. -/
example : operandSizeDefault? false 0xFF (some 4) = some .sixtyFour := rfl

/-- `/6` is `push r/m`: second group. -/
example : operandSizeDefault? false 0xFF (some 6) = some .sixtyFour := rfl

/-- `/3` is a **far** call, which the manual's parenthetical excludes. Getting
this one wrong is the easiest mistake in the whole rule, because it sits between
two neighbours that are both in the group. -/
example : operandSizeDefault? false 0xFF (some 3) = some .standard := rfl

/-- `/5` is a far jump, excluded for the same reason. -/
example : operandSizeDefault? false 0xFF (some 5) = some .standard := rfl

/-- `/0` is `inc`, an ordinary instruction. -/
example : operandSizeDefault? false 0xFF (some 0) = some .standard := rfl

/-- Asking about `FF` without a digit is unanswerable, and is refused rather
than guessed. -/
example : operandSizeDefault? false 0xFF none = none := rfl

/-! ## The first group, and the unmodeled rest -/

/-- `lea` follows the default. -/
example : operandSizeDefault? false 0x8D none = some .standard := rfl
/-- and so does group1 `imm8`, which is `sub r64, imm8`'s opcode. -/
example : operandSizeDefault? false 0x83 none = some .standard := rfl

/-- An opcode this profile does not model returns `none`, not `standard`.
Guessing `standard` would silently drop a `REX.W` an instruction needed. -/
example : operandSizeDefault? false 0x00 none = none := rfl
example : operandSizeDefault? true 0x00 none = none := rfl

/-! ## The model explains the encoders

The two facts `Width.default64BitMode`'s docstring said were "not derivable from
this constant". They are derivable from the function, and these are the pair
that shows it: the same library emits one instruction with `REX.W` and one
without, and the model says which is which. -/

/-- `pushR64` never emits `REX.W`, because `50+rd` is in the second group and
already has a 64-bit operand. -/
theorem pushR64_no_rexW (r : Gpr) :
    ∀ p, (pushR64 r).rex = some p → p.w = 0 := by
  intro p hp
  simp only [pushR64] at hp
  split at hp
  · cases hp; rfl
  · exact absurd hp (by simp)

/-- `subR64Imm8` always emits `REX.W`, because `83` is `standard` and a 64-bit
operand has to be asked for. -/
theorem subR64Imm8_needs_rexW (r : Gpr) (v : BitVec 8) :
    ∀ p, (subR64Imm8 r v).rex = some p → p.w = 1 := by
  intro p hp
  simp only [subR64Imm8, Option.some.injEq] at hp
  subst hp
  rfl

end Tests.ISA.X86.OperandSizeDefault
