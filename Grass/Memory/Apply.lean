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

## How this relates to `step`, exactly

`applyAccess` is **not** what the transition relation calls. `Grass/Op/Step.lean`
has its own `performAccess`, which does event minting and ledger work `applyAccess`
knows nothing about, and it is `step` that a program runs through.

What ties them is `MemoryState.commit`: every access that commits, commits
through it. So the framing results here are results about the transition, and
`Op.performAccess_frames_untouched` and `Op.runAccesses_frames_untouched` are
those results stated for `performAccess` and `runAccesses` directly.

`Op.step_frames_untouched` carries it to a whole operation. That theorem was
missing for several rounds while four documents claimed it existed, which mattered:
`runStep`'s faulting branch frames over `visibleEffects?`, which *excludes* the
faulting substep, so the survivor-list law is not a law about the step. It
quantifies over `sequence.accesses` instead, which contains both.

This is spelled out because an earlier version of this comment claimed
`applyAccess` had been *factored out of* `performAccess` when it had been written
alongside it — two write paths, framing proved about one, prose implying it
covered both. Review found it. `commit` is the repair.

What is still true and worth saying plainly: a straight-line argument over
`runBlock` is an argument about `applyAccess`, not about `step`. The two agree on
memory, and nothing yet proves they agree on the trace.

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
Why the state refuses one access, or `none` if it authorizes it.

Checked before anything commits, so a denial leaves the state exactly as it was
(`docs/MEMORY_MODEL.md` §1). The order is deliberate: liveness before space before
bounds before permission before initialization, so the recorded class names the
first thing that was wrong rather than an incidental consequence.

Alignment is deliberately absent. `AccessDescriptor.WellFormedIn.aligned` already
checks it and `step` requires well-formedness before any access is attempted, so a
misaligned access is *rejected at the declaration*, never denied at the state. An
alignment branch here would be unreachable, and an unreachable branch that looks
like a check is worse than no branch: it suggests the transition tests something
it does not. `AuditViolationClass.misaligned` remains for a profile whose own
alignment rule is stricter than the declared demand.

Authority beyond what an allocation record means is not here: loans, frames,
pins, and lock tokens are `Grass/Op/Step.lean`'s `AuthorityProvider` and need a
policy. This is memory's own rules, which is why it lives in the memory layer.
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
Commit an access's written bytes to memory.

**The single path by which an access commits.** `Grass/Op/Step.lean`'s
`performAccess` and `applyAccess` below both go through this, so the framing laws
stated here are laws about the transition and not about a parallel implementation
that happens to agree. An earlier arrangement had the two writing memory
separately, which is the same two-sources-of-truth defect this branch removed from
`AllocationRecord`, and review found it.

Not the single *write* primitive: that is `MemoryState.write`, which `commit`
wraps and which `Grass/Memory/Shape.lean`'s `writeField` also calls, since a
typed field store is not an access. An earlier version of this paragraph said
"the single write path" flatly and review corrected it. What is true is narrower
and is the thing the laws need: every `AccessDescriptor` that commits, commits
here.

`none` means the access wrote nothing, which is not the same as writing zero
bytes: a read commits no write at all.
-/
def MemoryState.commit (state : MemoryState) (d : AccessDescriptor)
    (written : Option ByteSeq) : MemoryState :=
  match written with
  | Option.none => state
  | some bytes => state.write d.provenance.root d.range.start bytes d.producesInitialized

/-- `WrittenFits d written` bounds committed bytes by the range the access
declared. `Committed.writtenFits` is where the transition gets it; `applyAccess`
gets it by truncating. Without it a commit could write past the declared range
and every framing argument stated over `d.range` would be false. -/
def WrittenFits (d : AccessDescriptor) (written : Option ByteSeq) : Prop :=
  ∀ bytes, written = some bytes → bytes.length ≤ d.range.size

/--
**A commit frames every cell the access did not declare.**

The law both write paths inherit. Stated over the *declared* range, which is what
a caller reads off a descriptor, and sound because `WrittenFits` bounds what was
actually written by it.
-/
theorem cellAt?_commit_of_untouched (state : MemoryState) (d : AccessDescriptor)
    {written : Option ByteSeq} (hfits : WrittenFits d written) {id : AllocId} {offset : Nat}
    (h : ¬ (d.provenance.root = id ∧ d.range.Covers offset)) :
    (state.commit d written).cellAt? id offset = state.cellAt? id offset := by
  unfold MemoryState.commit
  cases hw : written with
  | none => rfl
  | some bytes =>
    refine MemoryState.cellAt?_write_of_not_covers state d.provenance.root ?_
    by_cases hid : id = d.provenance.root
    · subst hid
      refine Or.inr fun hin => h ⟨rfl, ?_⟩
      have hlen := hfits bytes hw
      simp only [ByteRange.covers_def] at hin ⊢
      omega
    · exact Or.inl hid

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
      , state.commit d (if d.intent.writes then some (writeData.take d.range.size)
                        else Option.none) )

/-! ## The laws

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4 lists what the symbolic verifier consumes.
These are the ones about memory alone; the ones about events, obligations, and
the audit ledger are `Grass/Op/Step.lean`'s.

Framing is stated over cells rather than over states, deliberately. Two writes to
disjoint ranges leave the byte store's write history in different orders, so the
states are not equal and no amount of proving will make them equal. What is true
is that they agree at every offset, in byte *and* in initialization — the second
half matters because `denialOf` reads initialization, so a values-only agreement
would not carry the refusal decision. `docs/OLEAN_SHARDING.md` §1 asks for facts to cross the boundary as
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
  unfold applyAccess MemoryState.commit
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

/--
**Agreeing states decide the same way.**

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 recorded that `MemoryState.AgreesOn` does
not carry the refusal decision, and that a caller wanting decision stability had to
assemble it. This is that assembly, and it makes plain why cells alone were never
enough: `denialOf` reads five metadata fields as well as initialization, so two
states can agree at every byte and refuse differently. Review built exactly that
pair.

With both halves it goes through. Metadata agreement covers liveness, epoch,
space, bounds and permission directly, and with cell agreement it also gives
initialization by `rangeInitialized_congr_of_agrees`.
-/
theorem denialOf_congr_of_agrees {a b : MemoryState} {d : AccessDescriptor}
    (hmeta : a.MetadataAt d.provenance.root = b.MetadataAt d.provenance.root)
    (hcells : a.AgreesOn b) : denialOf a d = denialOf b d := by
  unfold denialOf
  simp only [MemoryState.rangeInitialized_congr_of_agrees hmeta hcells]
  unfold MemoryState.MetadataAt at hmeta
  cases ha : a.allocations.lookup d.provenance.root with
  | none =>
    rw [ha] at hmeta
    cases hb : b.allocations.lookup d.provenance.root with
    | none => rfl
    | some rb => rw [hb] at hmeta; simp at hmeta
  | some ra =>
    rw [ha] at hmeta
    cases hb : b.allocations.lookup d.provenance.root with
    | none => rw [hb] at hmeta; simp at hmeta
    | some rb =>
      rw [hb] at hmeta
      simp only [Option.map_some, Option.some.injEq] at hmeta
      have he : ra.extent = rb.extent :=
        congrArg AllocationRecord.Metadata.extent hmeta
      have hep : ra.epoch = rb.epoch :=
        congrArg AllocationRecord.Metadata.epoch hmeta
      have hsp : ra.space = rb.space :=
        congrArg AllocationRecord.Metadata.space hmeta
      have hpe : ra.permission = rb.permission :=
        congrArg AllocationRecord.Metadata.permission hmeta
      have hli : ra.live = rb.live :=
        congrArg AllocationRecord.Metadata.live hmeta
      simp only []
      rw [he, hep, hsp, hpe, hli]

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
through: the byte store is a journal, so the two orders leave different write
histories and no proof could make those states equal. `AgreesOn` compares *cells*,
so it carries initialization as well as values. It does not carry the refusal
decision — `denialOf` reads allocation metadata too — and an earlier version of
this paragraph said it did.

Read the conclusion precisely: it is about the resulting *state*, not about the
`AccessResult`s. Decision stability is a proof ingredient rather than part of what
is concluded — `denialOf_applyAccess_of_disjoint` is needed because without it one
order could refuse what the other committed and no fact about bytes would rescue
that, but the theorem does not itself state that neither order refuses.
`observedBytes_congr` is the piece a caller needs to carry an observation across,
and `applyAccess_result_comm` below is the result-level statement — which this
paragraph said was not proved here, seventy lines above the proof, until review
caught it.

Both accesses must lie in one allocation, which `hroot` requires.
`applyAccess_comm_of_other_allocation` and
`applyAccess_result_comm_of_other_allocation` are the cross-allocation pair, where
disjointness is free because distinct `AllocId`s are distinct storage.
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

/-- Two states agreeing over an access's range give it the same observation. The
lemma a caller uses to carry a read across a write it has framed. -/
theorem observedBytes_congr {a b : MemoryState} (d : AccessDescriptor)
    (indeterminate : Nat → Byte)
    (h : ∀ offset, offset < d.range.size →
      a.byteAt? d.provenance.root (d.range.start + offset) =
        b.byteAt? d.provenance.root (d.range.start + offset)) :
    observedBytes a d indeterminate = observedBytes b d indeterminate := by
  unfold observedBytes
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [h i hi]

/--
**An access gets the same result whichever side of a disjoint access it runs on.**

The half `applyAccess_comm` does not conclude. That theorem is about the resulting
state; this is about the `AccessResult`, which is both the refusal decision and the
observed bytes. Together they say a disjoint pair commutes in every respect the
model records, which is what §4's "reads and writes to disjoint ranges commute"
asks for and what §4.2 recorded as still owed.

Both halves come from framing rather than from anything new:
`denialOf_applyAccess_of_disjoint` for the decision, and
`applyAccess_frames_disjoint_range` fed through `observedBytes_congr` for the read.
-/
theorem applyAccess_result (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) :
    (applyAccess state d writeData indeterminate).1 =
      match denialOf state d with
      | some class_ => AccessResult.refused class_
      | Option.none =>
          { observed :=
              if d.intent.reads then some (observedBytes state d indeterminate)
              else Option.none
            refusal := Option.none } := by
  unfold applyAccess
  cases denialOf state d <;> rfl

theorem applyAccess_result_comm (state : MemoryState) (dA dB : AccessDescriptor)
    (writeA writeB : ByteSeq) (indetA indetB : Nat → Byte)
    (hroot : dA.provenance.root = dB.provenance.root)
    (hd : dA.range.Disjoint dB.range) :
    (applyAccess (applyAccess state dB writeB indetB).2 dA writeA indetA).1 =
      (applyAccess state dA writeA indetA).1 := by
  have hobs : observedBytes (applyAccess state dB writeB indetB).2 dA indetA =
      observedBytes state dA indetA := by
    refine observedBytes_congr dA indetA (fun offset hlt => ?_)
    have hcov : dA.range.Covers (dA.range.start + offset) :=
      ByteRange.covers_of (Nat.le_add_right _ _) (by omega)
    have := applyAccess_frames_disjoint_range state dB writeB indetB hd.symm hcov
    rw [← hroot] at this
    exact this
  rw [applyAccess_result, applyAccess_result,
    denialOf_applyAccess_of_disjoint state dB dA writeB indetB hroot.symm hd.symm, hobs]

/-! ### Accesses in different allocations

`applyAccess_comm` and `applyAccess_result_comm` need disjoint ranges because they
are about one allocation. Across allocations disjointness is free:
`docs/MEMORY_MODEL.md` §2 makes distinct `AllocId`s distinct storage by
construction, so offsets that happen to coincide are not the same bytes. §4.2
recorded these as unstated with `denialOf_write_of_other_allocation` as the
decision half; here they are. -/

/-- An access to another allocation does not change whether `d` is refused. -/
theorem denialOf_applyAccess_of_other_allocation (state : MemoryState)
    (dA dB : AccessDescriptor) (writeData : ByteSeq) (indeterminate : Nat → Byte)
    (hne : dB.provenance.root ≠ dA.provenance.root) :
    denialOf (applyAccess state dA writeData indeterminate).2 dB = denialOf state dB := by
  rw [applyAccess_state]
  split
  · exact denialOf_write_of_other_allocation state dB hne _ _ _
  · rfl

/-- **Accesses in different allocations commute**, in the resulting state. -/
theorem applyAccess_comm_of_other_allocation (state : MemoryState) (dA dB : AccessDescriptor)
    (writeA writeB : ByteSeq) (indetA indetB : Nat → Byte)
    (hne : dA.provenance.root ≠ dB.provenance.root) :
    (applyAccess (applyAccess state dA writeA indetA).2 dB writeB indetB).2.AgreesOn
      (applyAccess (applyAccess state dB writeB indetB).2 dA writeA indetA).2 := by
  rw [applyAccess_state (applyAccess state dA writeA indetA).2 dB writeB indetB,
    applyAccess_state (applyAccess state dB writeB indetB).2 dA writeA indetA,
    denialOf_applyAccess_of_other_allocation state dA dB writeA indetA (Ne.symm hne),
    denialOf_applyAccess_of_other_allocation state dB dA writeB indetB hne,
    applyAccess_state state dA writeA indetA, applyAccess_state state dB writeB indetB]
  by_cases hA : denialOf state dA = Option.none ∧ dA.intent.writes = true
  · by_cases hB : denialOf state dB = Option.none ∧ dB.intent.writes = true
    · simp only [if_pos hA, if_pos hB]
      exact MemoryState.write_comm_of_ne state hne _ _ _ _ _ _
    · simp only [if_pos hA, if_neg hB]
      exact MemoryState.AgreesOn.refl _
  · by_cases hB : denialOf state dB = Option.none ∧ dB.intent.writes = true
    · simp only [if_neg hA, if_pos hB]
      exact MemoryState.AgreesOn.refl _
    · simp only [if_neg hA, if_neg hB]
      exact MemoryState.AgreesOn.refl _

/-- **And in their results.** The same access gets the same decision and observes
the same bytes on either side of an access to a different allocation. -/
theorem applyAccess_result_comm_of_other_allocation (state : MemoryState)
    (dA dB : AccessDescriptor) (writeA writeB : ByteSeq) (indetA indetB : Nat → Byte)
    (hne : dA.provenance.root ≠ dB.provenance.root) :
    (applyAccess (applyAccess state dB writeB indetB).2 dA writeA indetA).1 =
      (applyAccess state dA writeA indetA).1 := by
  have hobs : observedBytes (applyAccess state dB writeB indetB).2 dA indetA =
      observedBytes state dA indetA := by
    refine observedBytes_congr dA indetA (fun offset _ => ?_)
    exact applyAccess_frames_other_allocation state dB writeB indetB hne _
  rw [applyAccess_result, applyAccess_result,
    denialOf_applyAccess_of_other_allocation state dB dA writeB indetB hne, hobs]

/-! ## Straight-line blocks

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4's exit criterion is that the framing set
suffices to discharge a straight-line Spike 1 block *without a bespoke local
lemma*. A block is a list of accesses run in order, and the law it needs is that
a byte no step touched is the byte it was before the block began.

The hypothesis is stated over each step's declared `range` rather than over the
bytes it actually wrote. That is the weaker fact and the useful one: a caller
reasoning about a block knows the ranges from the descriptors, and does not know
how much data each store carried. `applyAccess` only ever writes inside the
declared range, so the stronger hypothesis would buy nothing and cost every
caller an extra obligation.
-/

/-- Run a block of accesses in order, threading the state. -/
def runBlock (state : MemoryState) (indeterminate : Nat → Byte) :
    List (AccessDescriptor × ByteSeq) → List AccessResult × MemoryState
  | [] => ([], state)
  | (d, writeData) :: rest =>
      let step := applyAccess state d writeData indeterminate
      let after := runBlock step.2 indeterminate rest
      (step.1 :: after.1, after.2)

/--
**What memory looks like afterwards does not depend on what an indeterminate read
would have observed.**

`indeterminate` answers reads of bytes the store has no value for. This says that
answer stays in the observation and never reaches memory — so a profile choosing
differently changes what a program *sees*, never what it *leaves behind*. Without
it every downstream fact about a block's final state would be parameterized by a
choice that provably does not affect it.
-/
theorem applyAccess_state_indep (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (ind ind' : Nat → Byte) :
    (applyAccess state d writeData ind).2 = (applyAccess state d writeData ind').2 := by
  rw [applyAccess_state, applyAccess_state]

/-- `step.Touches id offset` holds when this step's declared range covers that
byte of that allocation. Everything else the step provably leaves alone. -/
def Touches (step : AccessDescriptor × ByteSeq) (id : AllocId) (offset : Nat) : Prop :=
  step.1.provenance.root = id ∧ step.1.range.Covers offset

instance (step : AccessDescriptor × ByteSeq) (id : AllocId) (offset : Nat) :
    Decidable (Touches step id offset) := inferInstanceAs (Decidable (_ ∧ _))

/-- **One access frames every cell it does not touch**, byte and initialization
together. The cell-level form the block law is built from. -/
theorem cellAt?_applyAccess_of_untouched (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte) {id : AllocId} {offset : Nat}
    (h : ¬ Touches (d, writeData) id offset) :
    (applyAccess state d writeData indeterminate).2.cellAt? id offset =
      state.cellAt? id offset := by
  rw [applyAccess_state]
  split
  · refine MemoryState.cellAt?_write_of_not_covers state d.provenance.root ?_
    by_cases hid : id = d.provenance.root
    · subst hid
      refine Or.inr fun hin => h ⟨rfl, ?_⟩
      simp only [ByteRange.covers_def, List.length_take] at hin ⊢
      omega
    · exact Or.inl hid
  · rfl

/--
**A straight-line block frames every cell no step of it touches.**

The exit criterion's lemma. A caller discharges a block by checking each step's
declared range against the bytes it cares about — which is decidable, and is what
`Touches` is for — and needs nothing else about what the block did.
-/
theorem cellAt?_runBlock_of_untouched (indeterminate : Nat → Byte) :
    ∀ (block : List (AccessDescriptor × ByteSeq)) (state : MemoryState) {id : AllocId}
      {offset : Nat}, (∀ step ∈ block, ¬ Touches step id offset) →
      (runBlock state indeterminate block).2.cellAt? id offset = state.cellAt? id offset
  | [], _, _, _, _ => rfl
  | (d, writeData) :: rest, state, id, offset, hall => by
    rw [runBlock,
      cellAt?_runBlock_of_untouched indeterminate rest _
        (fun step hstep => hall step (List.mem_cons_of_mem _ hstep)),
      cellAt?_applyAccess_of_untouched state d writeData indeterminate
        (hall (d, writeData) List.mem_cons_self)]

/-- The same independence for a whole block. -/
theorem runBlock_state_indep (ind ind' : Nat → Byte) :
    ∀ (block : List (AccessDescriptor × ByteSeq)) (state : MemoryState),
      (runBlock state ind block).2 = (runBlock state ind' block).2
  | [], _ => rfl
  | (d, writeData) :: rest, state => by
    rw [runBlock, runBlock, applyAccess_state_indep state d writeData ind ind',
      runBlock_state_indep ind ind' rest _]

/-- The byte form, which is what a load's observation is read through. -/
theorem byteAt?_runBlock_of_untouched (indeterminate : Nat → Byte)
    (block : List (AccessDescriptor × ByteSeq)) (state : MemoryState) {id : AllocId}
    {offset : Nat} (hall : ∀ step ∈ block, ¬ Touches step id offset) :
    (runBlock state indeterminate block).2.byteAt? id offset = state.byteAt? id offset := by
  rw [MemoryState.byteAt?_eq_map_cellAt?, MemoryState.byteAt?_eq_map_cellAt?,
    cellAt?_runBlock_of_untouched indeterminate block state hall]

/--
**What a step wrote survives the rest of the block.**

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4's exit criterion, stated as one theorem: a
store's bytes are still there at the end of a straight-line block, provided no
later step's declared range covers them. Everything a caller must check is
decidable from the descriptors — `Touches` is — so discharging a block is
checking ranges rather than reasoning about the store.
-/
theorem byteAt?_write_survives_block (state : MemoryState) (d : AccessDescriptor)
    (writeData : ByteSeq) (indeterminate : Nat → Byte)
    (block : List (AccessDescriptor × ByteSeq)) {record : AllocationRecord}
    (hfound : state.allocations.lookup d.provenance.root = some record)
    (hden : denialOf state d = Option.none) (hwrites : d.intent.writes = true)
    {offset : Nat}
    (hcov : (ByteRange.mk d.range.start (writeData.take d.range.size).length).Covers offset)
    (hall : ∀ step ∈ block, ¬ Touches step d.provenance.root offset) :
    (runBlock (applyAccess state d writeData indeterminate).2 indeterminate
        block).2.byteAt? d.provenance.root offset =
      (writeData.take d.range.size)[offset - d.range.start]? := by
  rw [byteAt?_runBlock_of_untouched indeterminate block _ hall, applyAccess_state,
    if_pos (And.intro hden hwrites)]
  exact MemoryState.byteAt?_write_of_covers _ hfound hcov

end Grass.Memory
