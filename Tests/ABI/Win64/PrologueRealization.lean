import Grass.ABI.Win64.UnwindBytes

/-!
# The prologue-realization counterexamples

`Grass.ABI.Win64.Layout.WellFormed` records an open obligation: its conditions
are internal, so a layout claiming three two-byte pushes end at 1, 2 and 3, or
claiming `SizeOfProlog = 255` for a ten-byte prologue, satisfies it and still
mis-unwinds. `Layout.Realizes` closes it by encoding the operations and
comparing offsets against bytes.

These are the fixtures that show it works, and they live here rather than
beside the definition because two of the three are deliberately *wrong*
layouts. A counterexample is test data: putting it in the library would add
three declarations to the trust ledger that model no external behaviour
truthfully, and the ledger has no honest category for that.

Each theorem below comes in a pair -- `WellFormed` holds, `Realizes` does not.
The pairing is the content. A counterexample that failed both predicates would
show nothing, because `WellFormed` would already have caught it.
-/

namespace Tests.ABI.Win64.PrologueRealization

open Grass.ABI.Win64 Grass.ISA.X86

/-- A real prologue: `push rbx; push rbp; push r12; sub rsp, 32`. One byte, one
byte, two bytes, four bytes -- so the offsets are 1, 2, 4, 8 and the prologue is
eight bytes long. -/
def realisticPrologue : Layout :=
  ⟨[ ⟨.pushNonvolatile .rbx, 1⟩
   , ⟨.pushNonvolatile .rbp, 2⟩
   , ⟨.pushNonvolatile .r12, 4⟩
   , ⟨.allocSmall 32, 8⟩ ], 8⟩

theorem realisticPrologue_wellFormed : realisticPrologue.WellFormed := by decide

/-- And it is realizable, which is the positive half: `Realizes` is not refusing
everything. -/
theorem realisticPrologue_realizes : realisticPrologue.Realizes := by decide

/-- The first counterexample from `WellFormed`'s docstring: three two-byte
pushes claiming to end at 1, 2 and 3. Extended registers need a `REX` prefix, so
each `push` is two bytes and the offsets must be 2, 4 and 6. -/
def misplacedPushes : Layout :=
  ⟨[ ⟨.pushNonvolatile .r12, 1⟩
   , ⟨.pushNonvolatile .r13, 2⟩
   , ⟨.pushNonvolatile .r14, 3⟩ ], 3⟩

theorem misplacedPushes_wellFormed : misplacedPushes.WellFormed := by decide

/-- The offsets ascend, stay inside the prologue and avoid zero, and every one
of them is wrong. -/
theorem misplacedPushes_not_realizes : ¬ misplacedPushes.Realizes := by decide

/-- The second counterexample: a ten-byte prologue declaring
`SizeOfProlog = 255`. Windows treats every address below 255 as mid-prologue and
restores nothing. -/
def overlongSizeOfProlog : Layout :=
  ⟨[ ⟨.pushNonvolatile .r12, 2⟩
   , ⟨.pushNonvolatile .r13, 4⟩
   , ⟨.pushNonvolatile .r14, 6⟩
   , ⟨.allocSmall 32, 10⟩ ], 255⟩

theorem overlongSizeOfProlog_wellFormed : overlongSizeOfProlog.WellFormed := by
  decide

theorem overlongSizeOfProlog_not_realizes : ¬ overlongSizeOfProlog.Realizes := by
  decide

/-- The offsets in that layout are right; only `SizeOfProlog` is wrong. Fixing
just that field makes it realizable, which is what pins the failure on the field
rather than on the offsets. -/
theorem overlongSizeOfProlog_fixed :
    ({ overlongSizeOfProlog with sizeOfProlog := 10 } : Layout).Realizes := by
  decide

/-- An allocation of 128 bytes is a legal `allocSmall` that needs the seven-byte
`imm32` form, so its offset is 7 and not 4. A stride-based model gets this
wrong; the encoder does not. -/
theorem allocSmall_128_uses_imm32 :
    (Layout.mk [⟨.allocSmall 128, 7⟩] 7).Realizes := by decide

/-- The same layout with the offset the `imm8` form would give is refused. -/
theorem allocSmall_128_not_four_bytes :
    ¬ (Layout.mk [⟨.allocSmall 128, 4⟩] 4).Realizes := by decide

/-! ### `allocLarge`

A mutation run found this branch untested: replacing `allocLarge`'s `imm32`
encoding with the four-byte `imm8` form left every theorem above green, because
every fixture above allocates through `allocSmall`. The gap is the ordinary
one -- fixtures that all take the same branch cannot test the branch.
-/

/-- `sub rsp, 4096` is seven bytes: `48 81 EC` and a four-byte immediate. An
allocation this size has no `imm8` form to choose. -/
def largePrologue : Layout := ⟨[⟨.allocLarge 4096, 7⟩], 7⟩

theorem largePrologue_wellFormed : largePrologue.WellFormed := by decide

theorem largePrologue_realizes : largePrologue.Realizes := by decide

/-- The same allocation at the offset the `imm8` form would give. This is the
layout the mutation produced, and it is refused. -/
theorem largePrologue_not_four_bytes :
    ¬ (Layout.mk [⟨.allocLarge 4096, 4⟩] 4).Realizes := by decide

/-- A push and a large allocation together, so the two encodings compose: one
byte then seven, giving offsets 1 and 8. -/
def pushThenLargeAlloc : Layout :=
  ⟨[⟨.pushNonvolatile .rbx, 1⟩, ⟨.allocLarge 4096, 8⟩], 8⟩

theorem pushThenLargeAlloc_realizes : pushThenLargeAlloc.Realizes := by decide

/-- `allocLarge` at the boundary where the unwind encoding itself changes
shape: past `largeAllocScaledMax` the operation needs three slots rather than
two. The instruction does not change -- it is `imm32` on both sides -- which is
worth pinning, because the two ceilings are easy to conflate. -/
theorem largeAlloc_above_scaledMax_still_imm32 :
    (Layout.mk [⟨.allocLarge 524288, 7⟩] 7).Realizes := by decide

end Tests.ABI.Win64.PrologueRealization
