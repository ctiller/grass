import Grass.Memory.Access
import Grass.Memory.State

/-!
# Applying one access to memory

`docs/INSTRUCTIONS.md` §5's bounded decidable forward fragment needs a function
that takes a descriptor and a memory state and returns what was observed and what
memory looks like afterwards. `Grass/Op/Step.lean` has that behaviour, but tangled
with event minting, obligation ledgers, and the audit ledger, so nothing could
state a law about memory alone.

`applyAccess` is that function. It is total, it is executable, and the laws below
are equations over it rather than statements about a transition's branches.

## What it does not decide

Authority beyond what an allocation record means. `denialOf` checks liveness,
epoch, address space, bounds, permission, and initialization, because those are
what an `AllocationRecord` *is*. Loans, frames, pins, and lock tokens are
`Grass/Op/Step.lean`'s `AuthorityProvider`, and they need a policy. A caller that
uses `applyAccess` alone gets memory's own rules and not a profile's.

## Two parameters rather than two defaults

`writeData` is what the operation writes, which a descriptor does not carry: a
descriptor says which bytes an access touches and what it may do to them, and
putting values on it would make every well-formedness proof about ranges also
about contents.

`indeterminate` is what an uninitialized byte reads as. It is reached only when a
descriptor permits reading uninitialized bytes, because `denialOf` refuses an
access demanding `.allBytesInitialized` first — so the profile that admitted such
a read is the one that owes what it observes. A zero default here would be
`docs/FOUNDATION.md` law 8's permissive fallback: the program would observe a
definite value the machine never promised.
-/

namespace Grass.Memory

open Grass.Std.Logical

/--
Why this access is refused by memory's own rules, or `none`.

Every reason an `AllocationRecord` can refuse an access, in one place and one
order, so the recorded class names the first thing that was wrong.
`docs/MEMORY_MODEL.md` §1 requires the check to happen before anything commits;
`applyAccess` calls this first and commits only on `none`.
-/
def denialOf (state : MemoryState) (d : AccessDescriptor) : Option AuditViolationClass :=
  match state.allocations.lookup d.provenance.root with
  | Option.none => some .deadProvenance
  | some record =>
      if record.live ≠ true then some .deadProvenance
      else if record.epoch ≠ d.provenance.epoch then some .deadProvenance
      else if record.space ≠ d.provenance.space then some .wrongAddressSpace
      else if ¬ record.extent.Contains d.range then some .outOfBounds
      else if ¬ record.permission.Permits d.intent then some .permissionDenied
      else if d.initialization = .allBytesInitialized ∧
              ¬ state.RangeInitialized d.provenance.root d.range then
        some .uninitializedRead
      else Option.none

/-- What an access observed, or why it was refused. -/
structure AccessResult where
  /-- The bytes observed, if the access read and was not refused. -/
  observed : Option ByteSeq
  /-- Why it was refused, if it was. -/
  refusal : Option AuditViolationClass
deriving DecidableEq, Repr

namespace AccessResult

/-- A result that refused. -/
def refused (class_ : AuditViolationClass) : AccessResult := ⟨Option.none, some class_⟩

/-- `result.Committed` holds when the access was not refused. -/
def Committed (result : AccessResult) : Prop := result.refusal = Option.none

instance (result : AccessResult) : Decidable result.Committed :=
  inferInstanceAs (Decidable (_ = _))

end AccessResult

/-- The bytes `d` observes, reading uninitialized positions through
`indeterminate`. Always exactly `d.range.size` long. -/
def observedBytes (state : MemoryState) (d : AccessDescriptor)
    (indeterminate : Nat → Byte) : ByteSeq :=
  (List.range d.range.size).map fun i =>
    match state.byteAt? d.provenance.root (d.range.start + i) with
    | some byte => byte
    | Option.none => indeterminate i

/--
Apply one access to memory.

Total: every descriptor and every state produce a result. Refusal returns the
state unchanged, which is `applyAccess_refused_preserves_state`.
-/
def applyAccess (state : MemoryState) (d : AccessDescriptor) (writeData : ByteSeq)
    (indeterminate : Nat → Byte) : AccessResult × MemoryState :=
  match denialOf state d with
  | some class_ => (.refused class_, state)
  | Option.none =>
      ( { observed :=
            if d.intent.reads then some (observedBytes state d indeterminate)
            else Option.none
          refusal := Option.none }
      , if d.intent.writes then
          state.write d.provenance.root d.range.start (writeData.take d.range.size)
            d.producesInitialized
        else state )

/-! ## The laws

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4 lists what the symbolic verifier consumes.
These are the ones about memory alone; the ones about events, obligations, and
the audit ledger are `Grass/Op/Step.lean`'s.

Framing is stated over `byteAt?` rather than over states, deliberately. Two writes
to disjoint ranges leave the byte store's `runs` in different orders, so the
states are not equal and no amount of proving will make them equal. What is true
— and what every downstream argument actually uses — is that they agree at every
offset. `docs/OLEAN_SHARDING.md` §1 asks for facts to cross the boundary as
exported theorems rather than as a representation consumers unfold, which is the
same discipline seen from the other side.
-/

/-- **A refused access preserves the state.** `applyAccess_refused_preserves_state`
is `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4's first required law, and discharges
`docs/MEMORY_MODEL.md` §1's requirement that the check happen before anything
commits. -/
theorem applyAccess_refused_preserves_state (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {class_ : AuditViolationClass}
    (h : denialOf state d = some class_) :
    applyAccess state d writeData indeterminate = (.refused class_, state) := by
  simp [applyAccess, h]

/-- A refused access observes nothing. A refusal that still reported bytes would
let a denied read leak the storage it was denied. -/
theorem applyAccess_refused_observes_nothing (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {class_ : AuditViolationClass}
    (h : denialOf state d = some class_) :
    (applyAccess state d writeData indeterminate).1.observed = Option.none := by
  simp [applyAccess, h, AccessResult.refused]

/--
What `applyAccess` leaves in memory, in one equation.

Every framing law below goes through this rather than through `applyAccess`'s
branches, so a change to the branch structure moves one proof rather than all of
them.
-/
theorem applyAccess_state (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) :
    (applyAccess state d writeData indeterminate).2 =
      if denialOf state d = Option.none ∧ d.intent.writes = true then
        state.write d.provenance.root d.range.start (writeData.take d.range.size)
          d.producesInitialized
      else state := by
  unfold applyAccess
  cases hden : denialOf state d with
  | some c => simp
  | none => by_cases hw : d.intent.writes = true <;> simp [hw]

/-- A read-only access leaves memory untouched. -/
theorem applyAccess_read_preserves_state (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) (h : d.intent.writes = false) :
    (applyAccess state d writeData indeterminate).2 = state := by
  rw [applyAccess_state]
  simp [h]

/-- **An access frames every other allocation.** Distinct `AllocId`s are distinct
storage by construction, which is what `docs/MEMORY_MODEL.md` §2 means by making
provenance rather than address the authority. -/
theorem applyAccess_frames_other_allocation (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {other : AllocId}
    (hne : other ≠ d.provenance.root) (offset : Nat) :
    (applyAccess state d writeData indeterminate).2.byteAt? other offset =
      state.byteAt? other offset := by
  rw [applyAccess_state]
  split
  · unfold MemoryState.byteAt?
    rw [MemoryState.write_preserves_other_allocation state hne]
  · rfl

/-- **An access frames every range in its own allocation that it did not write.**
The pointwise form; `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4's "reads and writes to
disjoint ranges commute and frame", framing half. -/
theorem applyAccess_frames_uncovered_offset (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {offset : Nat}
    (hout : ¬ (ByteRange.mk d.range.start (writeData.take d.range.size).length).Covers
      offset) :
    (applyAccess state d writeData indeterminate).2.byteAt? d.provenance.root offset =
      state.byteAt? d.provenance.root offset := by
  rw [applyAccess_state]
  split
  · cases hfound : state.allocations.lookup d.provenance.root with
    | none => rw [MemoryState.write_of_missing state _ _ _ hfound]
    | some record =>
      rw [MemoryState.byteAt?_write_self _ _ _ _ hfound]
      unfold MemoryState.byteAt?
      rw [hfound]
      simp only [Option.bind_some]
      exact ByteStore.byteAt?_write_of_not_covers record.bytes hout
  · rfl

/-- The range-level framing law, which is the one a disjointness argument states:
an access confined to `d.range` leaves every byte of a disjoint range as it was. -/
theorem applyAccess_frames_disjoint_range (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {other : ByteRange}
    (hd : d.range.Disjoint other) {offset : Nat} (hcov : other.Covers offset) :
    (applyAccess state d writeData indeterminate).2.byteAt? d.provenance.root offset =
      state.byteAt? d.provenance.root offset := by
  refine applyAccess_frames_uncovered_offset state d writeData indeterminate ?_
  intro hin
  refine hd.not_covers ?_ hcov
  simp only [ByteRange.covers_def, List.length_take] at hin ⊢
  omega


/-! ### Denial is framed too

Every framing law above is about bytes. A commutation argument also needs that
the *decision* is stable: if writing elsewhere could change whether `d` is
refused, two accesses would not commute however their bytes behaved.
`denialOf_write_of_other_allocation`, `denialOf_write_of_disjoint`, and
`denialOf_applyAccess_of_disjoint` are the lemmas that rule it out.
-/

/-- A write to another allocation does not change whether `d` is refused. -/
theorem denialOf_write_of_other_allocation (state : MemoryState) (d : AccessDescriptor)
    {id : AllocId} (hne : d.provenance.root ≠ id) (start : Nat) (bytes : ByteSeq)
    (initializes : Bool) :
    denialOf (state.write id start bytes initializes) d = denialOf state d := by
  unfold denialOf
  simp only [MemoryState.write_preserves_other_allocation state hne,
    MemoryState.rangeInitialized_congr_of_lookup
      (MemoryState.write_preserves_other_allocation state hne start bytes initializes)]

/-- **A write to a disjoint range does not change whether `d` is refused.**

The initialization clause is the one that could have gone wrong: it is the only
part of `denialOf` that reads bytes rather than metadata, and
`ByteStore.initialized_write_iff_of_disjoint` is what makes it stable in both
directions. -/
theorem denialOf_write_of_disjoint (state : MemoryState) (d : AccessDescriptor)
    {start : Nat} {bytes : ByteSeq} {initializes : Bool}
    (hd : (ByteRange.mk start bytes.length).Disjoint d.range) :
    denialOf (state.write d.provenance.root start bytes initializes) d =
      denialOf state d := by
  unfold denialOf
  simp only [MemoryState.rangeInitialized_write_iff_of_disjoint state hd]
  cases hfound : state.allocations.lookup d.provenance.root with
  | none =>
    simp only [MemoryState.write_of_missing state start bytes initializes hfound, hfound]
  | some record =>
    rw [MemoryState.lookup_write_self state start bytes initializes hfound]

/-- Applying one access does not change whether a disjoint one is refused. -/
theorem denialOf_applyAccess_of_disjoint (state : MemoryState) (dA dB : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte)
    (hroot : dA.provenance.root = dB.provenance.root) (hd : dA.range.Disjoint dB.range) :
    denialOf (applyAccess state dA writeData indeterminate).2 dB = denialOf state dB := by
  rw [applyAccess_state]
  split
  · rw [hroot]
    refine denialOf_write_of_disjoint state dB ?_
    have hsub := (hd.symm.of_take writeData.length).symm
    simpa [ByteRange.take, List.length_take, Nat.min_comm] using hsub
  · rfl

/--
**Accesses to disjoint ranges commute.**

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4's "reads and writes to disjoint ranges
commute and frame", commutation half. Two accesses to disjoint ranges of one
allocation leave memory agreeing at every offset whichever order they ran in.

Agreement rather than equality, and that is not a weakening to make a proof go
through: the byte store is a journal, so the two orders leave `runs` in different
orders and no proof could make those states equal. Every argument downstream
reads memory through `byteAt?`, which is exactly what agrees.

Both halves are needed and neither is decorative. `denialOf_applyAccess_of_disjoint`
says the *decision* is stable — without it one order could refuse what the other
committed, and no fact about bytes would rescue that. `MemoryState.write_comm`
says the bytes agree once both commit.
-/
theorem applyAccess_comm (state : MemoryState) (dA dB : AccessDescriptor)
    (writeA writeB : ByteSeq) (indetA indetB : Nat → Byte)
    (hroot : dA.provenance.root = dB.provenance.root)
    (hd : dA.range.Disjoint dB.range) :
    (applyAccess (applyAccess state dA writeA indetA).2 dB writeB indetB).2.AgreesOn
      (applyAccess (applyAccess state dB writeB indetB).2 dA writeA indetA).2 := by
  have hdA : (ByteRange.mk dA.range.start (writeA.take dA.range.size).length).Disjoint
      (ByteRange.mk dB.range.start (writeB.take dB.range.size).length) := by
    have h1 := (hd.of_take writeB.length)
    have h2 := (h1.symm.of_take writeA.length).symm
    simpa [ByteRange.take, List.length_take, Nat.min_comm] using h2
  rw [applyAccess_state (applyAccess state dA writeA indetA).2 dB writeB indetB,
    applyAccess_state (applyAccess state dB writeB indetB).2 dA writeA indetA,
    denialOf_applyAccess_of_disjoint state dA dB writeA indetA hroot hd,
    denialOf_applyAccess_of_disjoint state dB dA writeB indetB hroot.symm hd.symm,
    applyAccess_state state dA writeA indetA,
    applyAccess_state state dB writeB indetB]
  by_cases hA : denialOf state dA = Option.none ∧ dA.intent.writes = true
  · by_cases hB : denialOf state dB = Option.none ∧ dB.intent.writes = true
    · simp only [if_pos hA, if_pos hB, hroot]
      exact MemoryState.write_comm state dB.provenance.root hdA
    · simp only [if_pos hA, if_neg hB]
      exact MemoryState.AgreesOn.refl _
  · by_cases hB : denialOf state dB = Option.none ∧ dB.intent.writes = true
    · simp only [if_neg hA, if_pos hB]
      exact MemoryState.AgreesOn.refl _
    · simp only [if_neg hA, if_neg hB]
      exact MemoryState.AgreesOn.refl _

end Grass.Memory
