import Grass.ABI.Win64.Convention

/-!
# Which registers carry which arguments

`Grass/ABI/Win64/Convention.lean` proves several things about
`argumentRegister`: that the registers are distinct
(`argumentRegister_injective`), that they are all volatile
(`argumentRegisters_volatile`), that indices past the fourth spill
(`argumentRegister_beyond`), and that the shadow space matches their count.

None of that pins *which* registers. Injectivity survives any permutation of
four distinct registers, and volatility survives replacing `r8` with `r10`,
which is also volatile -- so `argumentRegister 2 = some .r10` satisfied every
theorem in the module. A sweep confirmed it: three mutations of the mapping left
the whole repository green.

That is the same shape as the relocation codes in
`Tests/Platform/Win32/CoffFixture.lean`, and the same lesson: a distinctness
theorem is not a pin. It matters more here, because the mapping is the calling
convention -- a wrong entry misplaces every argument at every call site, and
the program still assembles, links and runs.
-/

namespace Tests.ABI.Win64.ConventionValues

open Grass.ABI.Win64 Grass.ISA.X86

/-! ## The four registers, in order -/

example : argumentRegister 0 = some .rcx := rfl
example : argumentRegister 1 = some .rdx := rfl
example : argumentRegister 2 = some .r8 := rfl
example : argumentRegister 3 = some .r9 := rfl
example : argumentRegister 4 = none := rfl

/-- The list spelling, pinned separately from the function even though
`argumentRegister_eq_argumentRegisters` now relates them. That theorem says they
agree; these say what they agree *on*, which it cannot. -/
example : argumentRegisters = [.rcx, .rdx, .r8, .r9] := rfl

/-! ## Not the System V order

The likely wrong answer, and the reason these fixtures name a competing mapping
rather than only the right one. System V passes integer arguments in `rdi`,
`rsi`, `rdx`, `rcx` -- overlapping Win64's set in two registers and agreeing on
the position of neither. A model built from the wrong manual satisfies
injectivity and volatility just as well.
-/

/-- Win64's first argument is `rcx`; System V's is `rdi`. -/
example : argumentRegister 0 ≠ some .rdi := by decide

/-- `rsi` carries no argument at all under Win64, and is nonvolatile here --
which is the sharper statement, since System V has it carrying the second. -/
example : ∀ i, argumentRegister i ≠ some .rsi := by
  intro i
  match i with
  | 0 | 1 | 2 | 3 => decide
  | _ + 4 => simp [Grass.ABI.Win64.argumentRegister]

/-- `rdx` is in both conventions but at different positions: second under
Win64, third under System V. Agreement on membership is not agreement on
order. -/
example : argumentRegister 1 = some .rdx ∧ argumentRegister 2 ≠ some .rdx := by
  decide

end Tests.ABI.Win64.ConventionValues
