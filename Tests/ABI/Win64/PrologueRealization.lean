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

/-! ### The six operations with no encoding

`UnwindOp.prologueInsns` covers three of the nine operations and returns `none`
for the rest, and the header claims it "refuses rather than guesses". Nothing
tested that claim until these, which is worth saying plainly: the positive
theorems above would all still hold if the refusal were broken.

They are stated over arbitrary registers, offsets and `SizeOfProlog` values,
because the claim is that no choice of those makes such a layout realizable.
A fixture would only show that one particular choice fails. -/

/-- `setFramePointer` is a `LEA` or a `MOV` whose form depends on the frame
offset, and this module does not choose between them. -/
theorem setFramePointer_never_realizes (r : Gpr) (off : Nat) (codeOff szp : BitVec 8) :
    ¬ (Layout.mk [⟨.setFramePointer r off, codeOff⟩] szp).Realizes :=
  Layout.not_realizes_of_unencodable (op := .setFramePointer r off)
    (by simp [Layout.prologue]) rfl

/-- `saveNonvolatile` is a `MOV` to a stack slot whose `ModR/M` form depends on
the offset's magnitude. -/
theorem saveNonvolatile_never_realizes (r : Gpr) (off : Nat) (codeOff szp : BitVec 8) :
    ¬ (Layout.mk [⟨.saveNonvolatile r off, codeOff⟩] szp).Realizes :=
  Layout.not_realizes_of_unencodable (op := .saveNonvolatile r off)
    (by simp [Layout.prologue]) rfl

/-- The far form, same reason. -/
theorem saveNonvolatileFar_never_realizes (r : Gpr) (off : Nat)
    (codeOff szp : BitVec 8) :
    ¬ (Layout.mk [⟨.saveNonvolatileFar r off, codeOff⟩] szp).Realizes :=
  Layout.not_realizes_of_unencodable (op := .saveNonvolatileFar r off)
    (by simp [Layout.prologue]) rfl

/-- `saveXmm128` needs an XMM register operand, which
`Grass.ISA.X86.encodeMemInsn` does not take. -/
theorem saveXmm128_never_realizes (r : Xmm) (off : Nat) (codeOff szp : BitVec 8) :
    ¬ (Layout.mk [⟨.saveXmm128 r off, codeOff⟩] szp).Realizes :=
  Layout.not_realizes_of_unencodable (op := .saveXmm128 r off)
    (by simp [Layout.prologue]) rfl

/-- The far form of the same. -/
theorem saveXmm128Far_never_realizes (r : Xmm) (off : Nat) (codeOff szp : BitVec 8) :
    ¬ (Layout.mk [⟨.saveXmm128Far r off, codeOff⟩] szp).Realizes :=
  Layout.not_realizes_of_unencodable (op := .saveXmm128Far r off)
    (by simp [Layout.prologue]) rfl

/-- `pushMachineFrame` has no instruction at all: the processor pushed the trap
frame before the function's first byte ran. Refusing it is the honest answer
rather than a limitation -- there is nothing to encode. -/
theorem pushMachineFrame_never_realizes (withCode : Bool) (codeOff szp : BitVec 8) :
    ¬ (Layout.mk [⟨.pushMachineFrame withCode, codeOff⟩] szp).Realizes :=
  Layout.not_realizes_of_unencodable (op := .pushMachineFrame withCode)
    (by simp [Layout.prologue]) rfl

/-- One unencodable operation refuses a layout whose other operations encode.

The `push` and the `sub` here carry exactly the offsets the encoder produces for
them, and only the middle operation is unknown. That is enough: no amount of
correctness elsewhere rescues a layout containing an operation this module
cannot encode.

An earlier version of this comment claimed that substituting `some []` for
`none` would make *this* layout be accepted. That is false, and measuring it is
what showed so: under the substitution the fold computes offsets `1, 1, 5`
against the declared `1, 5, 9` and refuses on the mismatch. The theorem does go
red under that substitution, but only because its own proof term stops
typechecking -- which is not the same thing and does not test the layout at all.
`zeroByteReading_accepts_this` below is the fixture that actually distinguishes
the two readings. -/
theorem mixed_with_unencodable_not_realizes :
    ¬ (Layout.mk [ ⟨.pushNonvolatile .rbx, 1⟩
                 , ⟨.setFramePointer .rbp 0, 5⟩
                 , ⟨.allocSmall 32, 9⟩ ] 9).Realizes :=
  Layout.not_realizes_of_unencodable (op := .setFramePointer .rbp 0)
    (by simp [Layout.prologue]) rfl


/-- The fixture that separates `none` from `some []`.

Refused today. Under the `some []` reading it is *accepted*, because the
declared offsets are exactly the ones a zero-byte `setFramePointer` produces.
Proved by `decide` rather than through `Layout.not_realizes_of_unencodable`, so
what it tests is the computation and not whether a lemma application still
elaborates.

It is deliberately not `WellFormed` -- two operations share the offset 1, so
`Ascends` fails. That is unavoidable and is itself the point: any layout the
zero-byte reading accepts must have an operation ending where the previous one
did. `Realizes` has to refuse it on its own rather than leaning on `WellFormed`
to catch it, because the two predicates are checked independently. -/
theorem zeroByteReading_accepts_this :
    ¬ (Layout.mk [ ⟨.pushNonvolatile .rbx, 1⟩
                 , ⟨.setFramePointer .rbp 0, 1⟩ ] 1).Realizes := by decide

/-- The single-operation version of the same witness. -/
theorem zeroByteReading_accepts_this_singleton :
    ¬ (Layout.mk [⟨.setFramePointer .rbp 0, 0⟩] 0).Realizes := by decide

/-! ### The encoding is exactly these operations

`Grass/ABI/Win64/Convention.lean` argues from the fact that `UNWIND_CODE` has no
opcode for mode state -- no `MXCSR`, no x87 control word, no direction flag -- so
`preserved` there rests on the callee's epilogue and not on the unwinder. That
argument is about the *absence* of operations, which is the kind of claim that
rots silently when someone adds one.

This is what makes it face something. -/

/-- The opcode nibbles the encoding uses, and no others.

`6` and `7` are absent because they are the reserved and unused slots, and the
mode-state opcodes are absent because the encoding has none. A constructor added
to `UnwindOp` must either reuse one of these nine values or falsify this, and
either way the argument in `Convention.lean` gets re-read. -/
example (op : UnwindOp) :
    op.opcode.toNat ∈ [0, 1, 2, 3, 4, 5, 8, 9, 10] := by
  cases op <;> simp [UnwindOp.opcode]

/-- Nine constructors and nine distinct opcodes.

The membership check alone would still pass if two constructors collapsed onto
one value, which would silently shrink the encoding while looking like nothing
had changed. Concrete witnesses are needed because `opcode` is not injective on
*operations* -- two pushes of different registers share opcode 0 -- only on the
constructor each one uses. -/
example : ([ (UnwindOp.pushNonvolatile .rbx).opcode
           , (UnwindOp.allocLarge 4096).opcode
           , (UnwindOp.allocSmall 32).opcode
           , (UnwindOp.setFramePointer .rbp 0).opcode
           , (UnwindOp.saveNonvolatile .rbx 8).opcode
           , (UnwindOp.saveNonvolatileFar .rbx 65536).opcode
           , (UnwindOp.saveXmm128 .xmm6 16).opcode
           , (UnwindOp.saveXmm128Far .xmm6 65536).opcode
           , (UnwindOp.pushMachineFrame false).opcode
           ] : List (BitVec 4)).Nodup := by decide


/-! ### Which generator `opInfo` reproduces for `setFramePointer`

`Grass/ABI/Win64/Unwind.lean` records a vendor disagreement: for
`UWOP_SET_FPREG`, `ml64` writes the frame *register* in `OpInfo` and `cl.exe`
writes the frame *offset*. Grass reproduces `ml64`. Nothing rests on it for the
unwinder, which takes the register from `FrameRegister` -- which is exactly why
it needs pinning rather than why it does not. A field nothing depends on can be
changed without any downstream failure, and the only check on it was the `ml64`
differential, which needs an assembler this build does not have. A mutation
replacing the nibble with 0 left every test green.

The example is the docstring's own, chosen because it is the one where the two
generators visibly differ. -/

/-- `lea rbp, [rsp+96]`: frame register 5, frame offset 6. Grass writes 5. -/
example : (UnwindOp.setFramePointer .rbp 96).opInfo = 5 := rfl

/-- And not 6, which is what `cl.exe` would write for the same frame. Stated as
its own example because the equation above would still hold if the two happened
to coincide, and this is a fixture chosen so they do not. -/
example : (UnwindOp.setFramePointer .rbp 96).opInfo ≠ 6 := by decide

/-- The offset that would have been written: 96/16. Pinned so the contrast
above cannot quietly stop being one -- if `FrameSpec`'s scaling changed, 6 might
no longer be the competing value and the example would still pass while testing
nothing. -/
example : BitVec.ofNat 4 (96 / 16) = (6 : BitVec 4) := rfl


end Tests.ABI.Win64.PrologueRealization
