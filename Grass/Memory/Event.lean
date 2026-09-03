import Grass.Core.Context
import Grass.Core.Name
import Grass.Core.Uid
import Grass.Memory.Access
import Grass.Std.Logical.Byte

/-!
# The common memory event vocabulary

`docs/MEMORY_MODEL.md` §7.1 fixes the fields a memory event must carry and adds
the rule that governs extension: "Profiles may add fields but may not reinterpret
common ones." `MemoryEvent` below carries exactly that list.

Events exist in M1, before the consistency graph that reads them (M8), for the
reason `docs/MEMORY_IMPLEMENTATION_PLAN.md` §7 gives: an instruction model that
declares its events now should not be rewritten when the graph arrives. The
relations over events — sequenced-before, reads-from, modification order,
synchronizes-with, happens-before — are M8 and are deliberately absent.

`Conflicts` is here rather than in M8 because §7.3 defines it structurally, from
ranges and intents alone, with no relation involved: "Two events conflict when
their live byte ranges overlap, at least one writes, and they are not both
compatible atomic accesses under one profile." What is *not* here is the
definition of a data race, which needs happens-before and therefore needs M8.
Conflict is a fact about two events; a race is a fact about an execution.
-/

namespace Grass.Memory

open Grass.Core Grass.Std.Logical

/-- Phantom tag for event identities. -/
inductive EventTag : Type

/-- The generative identity of one memory event. -/
abbrev EventId := Uid EventTag

/--
What produced an event.

The instruction or API identity is nominal here because the concrete
`RawInstruction` type belongs to the ISA profile, and this module must stay below
it. A profile refines this to its own instruction identity through its event
construction.
-/
structure EventCause where
  /-- The nominal identity of the instruction, API, or agent action. -/
  origin : Name
deriving DecidableEq, Repr

/--
What an event does at its location.

Exactly the five kinds `docs/MEMORY_MODEL.md` §7.1 names. A read-modify-write is
its own kind rather than a read event beside a write event, because the
consistency profile has to be able to say that nothing intervened between them.
-/
inductive EventKind where
  /-- Observes bytes. -/
  | read
  /-- Modifies bytes. -/
  | write
  /-- Observes and modifies indivisibly. -/
  | readModifyWrite
  /-- Orders other events without accessing bytes. -/
  | fence
  /-- Affects control flow, participating in dependency relations. -/
  | control
deriving DecidableEq, Repr

namespace EventKind

/-- Whether this kind observes bytes. -/
def reads : EventKind → Bool
  | .read | .readModifyWrite => true
  | .write | .fence | .control => false

/-- Whether this kind modifies bytes. -/
def writes : EventKind → Bool
  | .write | .readModifyWrite => true
  | .read | .fence | .control => false

/-- Whether this kind touches bytes at all. A fence and a control event have no
location, so they conflict with nothing. -/
def touchesMemory : EventKind → Bool
  | .read | .write | .readModifyWrite => true
  | .fence | .control => false

end EventKind

/--
One memory event.

Every field of `docs/MEMORY_MODEL.md` §7.1 is present: identity, context identity
and kind, cause, location and provenance, kind, values read and written,
atomicity and requested ordering, address space and memory type (both carried by
`space`), scope (carried by `ordering`), and status.
-/
structure MemoryEvent where
  /-- This event's generative identity. -/
  id : EventId
  /-- The context that performed it, with its kind. -/
  context : ExecutionContext
  /-- The instruction, API, or agent action that caused it. -/
  cause : EventCause
  /-- The address space, which carries the memory type and coherence. -/
  space : AddressSpace
  /-- The provenance of the location touched. -/
  provenance : Provenance
  /-- The byte range touched, relative to the provenance's root allocation. -/
  range : ByteRange
  /-- What the event does at that location. -/
  kind : EventKind
  /-- The bytes observed, if any. -/
  valueRead : Option ByteSeq
  /-- The bytes written, if any. -/
  valueWritten : Option ByteSeq
  /-- Atomicity, requested ordering, and scope. -/
  ordering : OrderingDemand
  /-- Whether the event completed, completed partially, or faulted. -/
  status : AccessStatus
  /-- How many bytes this event actually observed. -/
  readCommitted : Nat
  /-- How many bytes this event actually wrote. -/
  writeCommitted : Nat
deriving DecidableEq, Repr

namespace MemoryEvent

/--
The bytes this event actually observed.

Separate from the written range, because a read-modify-write can do one and not
the other. An `xadd` that read eight bytes and then faulted before storing has
`readCommitted = 8` and `writeCommitted = 0`; a single shared count would have
forced it to claim it read nothing, while `readValuePresent` still demanded a
value — so a faulted RMW could not be recorded at all.
-/
def committedReadRange (e : MemoryEvent) : ByteRange := e.range.take e.readCommitted

/-- The bytes this event actually wrote. -/
def committedWriteRange (e : MemoryEvent) : ByteRange := e.range.take e.writeCommitted

/-- The bytes this event touched at all, read or written. -/
def committedRange (e : MemoryEvent) : ByteRange :=
  e.range.take (max e.readCommitted e.writeCommitted)

/--
`e.WellFormed` holds when the event's values agree with what its kind claims.

An event whose kind says it reads but which carries no value read describes
nothing, and one carrying a value of the wrong length describes an effect
different from the one its status reports.
-/
structure WellFormed (e : MemoryEvent) : Prop where
  /-- A reading event carries the bytes it observed. -/
  readValuePresent : e.kind.reads = true → e.valueRead.isSome
  /-- A non-reading event carries no observed bytes. -/
  readValueAbsent : e.kind.reads = false → e.valueRead = Option.none
  /-- A writing event carries the bytes it wrote. -/
  writeValuePresent : e.kind.writes = true → e.valueWritten.isSome
  /-- A non-writing event carries no written bytes. -/
  writeValueAbsent : e.kind.writes = false → e.valueWritten = Option.none
  /-- A fence or control event has no location, so its range is empty. -/
  noLocationWhenUntouched : e.kind.touchesMemory = false → e.range.IsEmpty
  /-- Written bytes number exactly what the status says committed. This is what
  connects `docs/MEMORY_MODEL.md` §4's "a write initializes only the bytes it
  actually completes" to the event record. -/
  writtenLength :
    ∀ bytes, e.valueWritten = some bytes → bytes.length = e.committedWriteRange.size
  /-- Observed bytes number exactly what the event says it read. -/
  readLength :
    ∀ bytes, e.valueRead = some bytes → bytes.length = e.committedReadRange.size
  /-- Neither count exceeds the range. -/
  readWithinRange : e.readCommitted ≤ e.range.size
  /-- Neither count exceeds the range. -/
  writeWithinRange : e.writeCommitted ≤ e.range.size
  /-- The status does not claim more bytes than the range covers. -/
  statusWellFormed : e.status.WellFormed e.range.size
  /-- **The status and the counts are the same two facts.**

  An event records how much it read and wrote twice, once in `status` and once in
  its own fields, and nothing compared them: review built an event whose status
  said it observed nothing while `readCommitted` said eight, discharged every
  other clause by `decide`, and wrapped it in a `ValidMemoryEvent`. Two records of
  one fact with no clause tying them is the defect this layer keeps finding
  elsewhere, inside the structure that exists to prevent it. -/
  statusAgreesWithReads : e.status.committedReads = e.readCommitted
  /-- The write half of `statusAgreesWithReads`. -/
  statusAgreesWithWrites : e.status.committedWrites = e.writeCommitted
  /-- The event's address space is the one its provenance names.

  Two records of one fact, and nothing tied them. `space` is what the event reports
  while `provenance.space` is what the descriptor declared; the two agreed only because
  `Grass/Op/Step.lean`'s `performAccess` resolves the space through the profile's
  table before calling `ofOutcome`. `Conflicts` keyed on `provenance.space` when this
  clause was written and no longer does, which removes a consumer but not the
  objection: a structure carrying one fact twice with no clause tying them is the
  defect this layer keeps finding. That is the argument this structure exists to
  make unnecessary — it was rejected for the context identity in
  `StepRejection.contextMismatch` and for the status and count pair in the clause
  above — and review found it standing here, in a file no round had read. -/
  spaceAgreesWithProvenance : e.space.id = e.provenance.space

/--
`Conflicts a b` holds when two events contend for the same bytes.

`docs/MEMORY_MODEL.md` §7.3: two events conflict when "their live byte ranges
overlap, at least one writes, and they are not both **compatible atomic accesses
under one profile**."

The last clause is why `compatible` is a parameter rather than
`both are atomic`. Atomicity alone is not compatibility. A four-byte atomic load
overlapping an eight-byte atomic store is a mixed-size atomic access, compatible
under no profile this project targets; so is a `thread`-scoped atomic against a
`system`-scoped one, and a profile-specific ordering mode against a portable one.
Reading "not both atomic" as compatibility would silently declare all of those
non-conflicting, which is weaker than the corpus in the unsafe direction and
would be inherited by every race-freedom theorem built on it. `atomicsAreNever`
below is the conservative choice for a profile that has not yet stated a
compatibility relation.

Note carefully what this is *not*: a conflict is not a data race. A race
additionally requires the two events to be unordered by happens-before, which
needs the consistency graph of M8. Two conflicting events properly ordered by a
lock are not a race.

`sharesBytes` is the other parameter, and it replaces an earlier
`Provenance.SameStorage` clause that was wrong in the unsafe direction.
`SameStorage` demands equal `AllocId`s, so a host-visible device buffer and the
device allocation behind it, a `MapViewOfFile` view and the file it maps, and a
physical/virtual pair were all declared non-conflicting — while
`docs/MEMORY_MODEL.md` §7.5 explicitly contemplates mapping and sharing. Whether
two allocations name the same bytes is a fact about the machine state, not about
provenance, so `MemoryState.SharesBytes` supplies it.

Overlap is checked on the *committed* ranges, since bytes an event did not commit
are bytes it did not touch.
-/
def Conflicts (sharesBytes : AllocId → AllocId → Prop)
    (compatible : MemoryEvent → MemoryEvent → Prop) (a b : MemoryEvent) : Prop :=
  a.kind.touchesMemory = true ∧ b.kind.touchesMemory = true ∧
  sharesBytes a.provenance.root b.provenance.root ∧
  a.committedRange.Overlaps b.committedRange ∧
  (a.kind.writes = true ∨ b.kind.writes = true) ∧
  ¬ compatible a b

/--
The conservative compatibility relation: no pair of accesses is compatible.

A profile that has not stated which atomic pairs its target actually admits gets
this one, and every overlapping pair with a writer is then a conflict. That is
the safe direction: it can only cause a profile to demand more ordering than
strictly necessary, never less.
-/
def atomicsAreNever (_a _b : MemoryEvent) : Prop := False

instance (a b : MemoryEvent) : Decidable (atomicsAreNever a b) := .isFalse (fun h => h)

instance {sharesBytes : AllocId → AllocId → Prop}
    [∀ x y, Decidable (sharesBytes x y)]
    {compatible : MemoryEvent → MemoryEvent → Prop}
    [∀ x y, Decidable (compatible x y)] (a b : MemoryEvent) :
    Decidable (Conflicts sharesBytes compatible a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem Conflicts.symm {sharesBytes : AllocId → AllocId → Prop}
    {compatible : MemoryEvent → MemoryEvent → Prop}
    (shareSymm : ∀ x y, sharesBytes x y → sharesBytes y x)
    (symmetric : ∀ x y, compatible x y → compatible y x) {a b : MemoryEvent}
    (h : Conflicts sharesBytes compatible a b) :
    Conflicts sharesBytes compatible b a := by
  obtain ⟨ha, hb, hshare, ho, hw, hat⟩ := h
  refine ⟨hb, ha, shareSymm _ _ hshare, ?_, hw.symm,
    fun hc => hat (symmetric b a hc)⟩
  obtain ⟨offset, h₁, h₂⟩ := ho
  exact ⟨offset, h₂, h₁⟩

/-- Two reads never conflict, whatever their ordering. -/
theorem not_conflicts_of_both_read {sharesBytes : AllocId → AllocId → Prop}
    {compatible : MemoryEvent → MemoryEvent → Prop}
    {a b : MemoryEvent} (ha : a.kind = .read) (hb : b.kind = .read) :
    ¬ Conflicts sharesBytes compatible a b := by
  rintro ⟨_, _, _, _, hw, _⟩
  rw [ha, hb] at hw
  simp [EventKind.writes] at hw

/-- Events in different storage never conflict, however their offsets compare.
This is `docs/MEMORY_MODEL.md` §7.5 at the event layer. -/
theorem not_conflicts_of_unshared {sharesBytes : AllocId → AllocId → Prop}
    {compatible : MemoryEvent → MemoryEvent → Prop} {a b : MemoryEvent}
    (h : ¬ sharesBytes a.provenance.root b.provenance.root) :
    ¬ Conflicts sharesBytes compatible a b :=
  fun hc => h hc.2.2.1

/-!
**There is no theorem here saying different spaces never conflict, and there was.**

`Conflicts` carried `a.provenance.space = b.provenance.space` and that theorem
asserted the narrowing as a law of §7.5. §7.3's sentence has no address-space clause,
and §7.5's is about offset coincidence -- "not interchangeable *merely because their
offsets match*" -- which `sharesBytes` already implements: unrelated allocations do
not share bytes whatever their spaces, and related ones share them only where the
state says so.

The conjunct did not narrow the rule to offset coincidence. It cancelled a
*declared* sharing whenever the two provenances named different spaces, which is
exactly the configuration the `SameStorage` repair above was made for: two of the
three pairs that repair names -- a host-visible device buffer and the device
allocation behind it, a physical/virtual pair -- live in different spaces. Review
stepped it: with the buffer aliased to a host-visible device view, the program thread
wrote the buffer and the device engine then wrote the same declared storage through
the view, and the step committed with an empty violation ledger. The same store
through a *cpu*-space view of the same storage was refused as `conflictingAccess`.

`MemoryState.AuthorizedAt` had dropped its own space conjunct for the same reason and
said so, so the authority rule and the race rule were answering differently about one
pair of allocations.
-/

/-- **An event that touches no bytes conflicts with nothing.**

Stated over `touchesMemory` and not over `EventKind.fence`. It was
`(h : a.kind = .fence)`, and nothing in the model can mint an event of that kind, so
the theorem held of a term no state could reach.

**The correction moved the vacuity; it did not remove it, and an earlier version of
this docstring claimed otherwise** ("a real statement about a real hypothesis").
Review checked: `kindOf` yields only `read`, `write` and `readModifyWrite`, all three
of which `touchesMemory_kindOf` sends to `true`; `ofOutcome` is the only producer of a
`ValidMemoryEvent`; and `MachineState.events` holds `ValidMemoryEvent`. So no event in
any trace satisfies this hypothesis either — `touchesMemory_ofOutcome` below is that
fact, stated rather than left implicit.

The theorem is kept, because it is a true statement about `Conflicts` over arbitrary
`MemoryEvent`s and `Conflicts` is where a fence *would* enter if §7.1's fence kind
became constructible. What it is not is coverage of anything the transition can
produce, and this docstring says so now. The same applies to
`WellFormed.noLocationWhenUntouched`. -/
theorem not_conflicts_of_untouched {sharesBytes : AllocId → AllocId → Prop}
    {compatible : MemoryEvent → MemoryEvent → Prop}
    {a b : MemoryEvent} (h : a.kind.touchesMemory ≠ true) :
    ¬ Conflicts sharesBytes compatible a b := fun hc => h hc.1

end MemoryEvent

/-!
## Intent and outcome are different things

An `AccessDescriptor` is what an operation *intends*: a kind, an address, a width,
a provenance. It is static, so it does not carry the bytes that were read or
written: those are facts about the machine at the moment the access ran, and
`Committed` is where they live.
An earlier bridge tried to build an event from the descriptor alone and passed
`none` for both values — so **every event the transition minted violated
`MemoryEvent.WellFormed`**, a predicate the codebase stated, proved a lemma about,
and then contradicted at its only producer.

The repair is to give the outcome its own type, indexed by the intent it belongs
to. The transition supplies it from machine state, a device oracle, or a prior
substep's result. `MemoryEvent.ofOutcome` is the only producer of a
`ValidMemoryEvent`, and it discharges `MemoryEvent.WellFormed` itself, so the
trace cannot contain an event that skipped the check.
-/

/--
What an access actually committed.

Indexed by the descriptor, so the byte counts and the presence of each value are
tied to the intent that produced them. The fields are proofs, not conventions: a
`Committed` for a write-only intent cannot carry observed bytes, and neither value
can exceed the range the access named.

Read and write are counted separately, which is what lets a partial
read-modify-write keep its completed read. An `xadd` that observed eight bytes and
then faulted before storing has `observed = some bs` with `bs.length = 8` and
`written = none`.
-/
structure Committed (d : AccessDescriptor) where
  /-- The bytes observed, if the access reads. -/
  observed : Option ByteSeq
  /-- The bytes written, if the access writes. -/
  written : Option ByteSeq
  /-- A reading access observed something. -/
  observedPresent : d.intent.reads = true → observed.isSome
  /-- A non-reading access observed nothing. -/
  observedAbsent : d.intent.reads = false → observed = Option.none
  /-- A writing access wrote something. -/
  writtenPresent : d.intent.writes = true → written.isSome
  /-- A non-writing access wrote nothing. -/
  writtenAbsent : d.intent.writes = false → written = Option.none
  /-- Observed bytes fit the named range. -/
  observedFits : ∀ bytes, observed = some bytes → bytes.length ≤ d.range.size
  /-- Written bytes fit the named range. -/
  writtenFits : ∀ bytes, written = some bytes → bytes.length ≤ d.range.size

namespace Committed

variable {d : AccessDescriptor}

/-- How many bytes were observed. -/
def readCount (c : Committed d) : Nat := (c.observed.map List.length).getD 0

/-- How many bytes were written. -/
def writeCount (c : Committed d) : Nat := (c.written.map List.length).getD 0

theorem readCount_le (c : Committed d) : c.readCount ≤ d.range.size := by
  unfold readCount
  cases hobs : c.observed with
  | none => simp
  | some bytes => simpa using c.observedFits bytes hobs

theorem writeCount_le (c : Committed d) : c.writeCount ≤ d.range.size := by
  unfold writeCount
  cases hw : c.written with
  | none => simp
  | some bytes => simpa using c.writtenFits bytes hw

/-- The outcome of an access that touched nothing. Available only where the
intent reads and writes nothing, which `AccessDescriptor.WellFormedIn` already
rejects — so this exists for completeness rather than for use. -/
def inert (hr : d.intent.reads = false) (hw : d.intent.writes = false) :
    Committed d :=
  { observed := Option.none, written := Option.none
    observedPresent := fun h => absurd (hr ▸ h) (by simp)
    observedAbsent := fun _ => rfl
    writtenPresent := fun h => absurd (hw ▸ h) (by simp)
    writtenAbsent := fun _ => rfl
    observedFits := fun _ h => absurd h (by simp)
    writtenFits := fun _ h => absurd h (by simp) }

/--
Truncate a committed outcome to a prefix, for a faulting access.

**Reads and writes truncate separately**, which is the whole reason `Committed`
counts them separately. This module's own docstrings motivate the two-count design
with an `xadd` that observed eight bytes and then faulted before storing any — and
until review checked, the transition truncated both lists by one shared count, so
that outcome was the one thing the fault path could not express. A faulting
read-modify-write always reported `readCommitted = writeCommitted`, and the
fixture asserting the read survived never checked the write, so it passed while
demonstrating the opposite of the property its section claimed.
-/
def truncate {d : AccessDescriptor} (c : Committed d) (reads writes : Nat) :
    Committed d :=
  { observed := c.observed.map (·.take reads)
    written := c.written.map (·.take writes)
    observedPresent := fun h => by simpa using c.observedPresent h
    observedAbsent := fun h => by simp [c.observedAbsent h]
    writtenPresent := fun h => by simpa using c.writtenPresent h
    writtenAbsent := fun h => by simp [c.writtenAbsent h]
    observedFits := by
      intro bytes hb
      obtain ⟨original, horig, rfl⟩ := Option.map_eq_some_iff.mp hb
      have := c.observedFits original horig
      simp only [List.length_take]
      omega
    writtenFits := by
      intro bytes hb
      obtain ⟨original, horig, rfl⟩ := Option.map_eq_some_iff.mp hb
      have := c.writtenFits original horig
      simp only [List.length_take]
      omega }

end Committed

/--
A `Committed` that filled the access it answers.

`Committed`'s length obligations are upper bounds — `observedFits` and
`writtenFits` say a committed list is *no longer* than the range, never that it
fills it. That is right for a faulting access, whose whole point is a prefix. It
is wrong for a completed one, and nothing said so: an oracle returning an empty
write for a nonempty store produced a `completed` outcome, `AccessOutcome.status`
quietly relabelled it `partialCommit 0 0`, and the operation continued to its
later substeps with nothing committed and no fault or denial. A malformed machine
answer became successful execution, which is the shape `docs/FOUNDATION.md` law 8
names. Review type-checked that counterexample against the seam fixture.

The counts are **intent-relative**: an access that does not read owes no read
bytes. Carrying the evidence here rather than checking it later makes a short
completion unrepresentable instead of detectable.
-/
structure CompleteCommitted (d : AccessDescriptor) where
  /-- What the machine committed. -/
  committed : Committed d
  /-- A reading access observed its whole range. -/
  readsFull : d.intent.reads = true → committed.readCount = d.range.size
  /-- A writing access wrote its whole range. -/
  writesFull : d.intent.writes = true → committed.writeCount = d.range.size

/--
What happened when an access was attempted.

`denied` carries no `Committed`, which is the type-level form of
`docs/MEMORY_MODEL.md` §1's "Denial preserves the state immediately before the
denied substep": a denial that reported committed bytes is not expressible.
-/
inductive AccessOutcome (d : AccessDescriptor) where
  /-- The access ran to completion, filling every count its intent implies.
  `CompleteCommitted` carries that evidence, so a short answer cannot be dressed
  as a completion. -/
  | completed (complete : CompleteCommitted d)
  /-- The access faulted, having committed what `committed` records. -/
  | faulted (fault : FaultClassId) (committed : Committed d)
  /-- The access was refused before committing anything. -/
  | denied (violation : AuditViolation)

namespace AccessOutcome

variable {d : AccessDescriptor}

/--
The architectural status this outcome reports.

The completeness test is **intent-relative**, and has to be. It once demanded
`readCount = size ∧ writeCount = size` unconditionally, so a write-only access —
whose `readCount` is `0` because `Committed.observedAbsent` requires it — could
never report `.completed`. Every ordinary load and store recorded
`.partialCommit`, whose own docstring says "stopped early without faulting", and
`AccessStatus.IsComplete` was false for every access this model can perform except
a full-width read-modify-write. Review found it by asking what a completed load
reports. `Tests/Op/FakeIsa.lean`'s `a_completed_load_reports_completed` is the
regression.
-/
def status : AccessOutcome d → AccessStatus
  | .completed c => .completed c.committed.readCount c.committed.writeCount
  | .faulted fault c => .faulted fault c.readCount c.writeCount
  | .denied _ => .partialCommit 0 0

/-- The violation this outcome records, if it was refused. -/
def violation? : AccessOutcome d → Option AuditViolation
  | .denied v => some v
  | .completed _ | .faulted _ _ => Option.none

/-- What this outcome committed, if it committed anything. -/
def committed? : AccessOutcome d → Option (Committed d)
  | .completed c => some c.committed
  | .faulted _ c => some c
  | .denied _ => Option.none

/-- A denial commits nothing, by construction rather than by convention. -/
@[simp] theorem committed?_denied (v : AuditViolation) :
    (AccessOutcome.denied (d := d) v).committed? = Option.none := rfl

/-- The status an outcome reports never claims more bytes than the access named.
`Committed` carries the bounds, so this is a projection rather than a check. -/
theorem status_wellFormed (outcome : AccessOutcome d) :
    outcome.status.WellFormed d.range.size := by
  cases outcome with
  | completed c =>
    exact ⟨c.committed.readCount_le, c.committed.writeCount_le⟩
  | faulted fault c =>
    exact ⟨c.readCount_le, c.writeCount_le⟩
  | denied _ =>
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩

end AccessOutcome

/--
A memory event together with the proof that it is well formed.

`docs/MEMORY_MODEL.md` §7.1 fixes what an event must carry, and a trace of
unconstrained `MemoryEvent` values beside an unused predicate is not that. The
trace holds these, so "every event in the trace is well formed" is true by
construction rather than by a check something might forget to run — and M8's
consistency model consumes a type that cannot contain a malformed event.
-/
structure ValidMemoryEvent where
  private mk ::
  /-- The event. -/
  event : MemoryEvent
  /-- Its well-formedness. -/
  wellFormed : event.WellFormed

namespace MemoryEvent

/--
The event kind an intent gives rise to, if any.

`none` for an inert intent, which reads and writes nothing. That case is already
rejected by `AccessDescriptor.WellFormedIn.notInert`; returning `none` rather than
picking a plausible kind keeps the rejection rather than papering over it
(`docs/FOUNDATION.md` law 8).
-/
def kindOf (intent : AccessIntent) : Option EventKind :=
  if intent.reads && intent.writes then some .readModifyWrite
  else if intent.writes then some .write
  else if intent.reads then some .read
  else Option.none

theorem reads_kindOf {intent : AccessIntent} {kind : EventKind}
    (h : kindOf intent = some kind) : kind.reads = intent.reads := by
  obtain ⟨reads, writes, _, _⟩ := intent
  cases reads <;> cases writes <;> simp [kindOf] at h <;> subst h <;> rfl

theorem writes_kindOf {intent : AccessIntent} {kind : EventKind}
    (h : kindOf intent = some kind) : kind.writes = intent.writes := by
  obtain ⟨reads, writes, _, _⟩ := intent
  cases reads <;> cases writes <;> simp [kindOf] at h <;> subst h <;> rfl

theorem touchesMemory_kindOf {intent : AccessIntent} {kind : EventKind}
    (h : kindOf intent = some kind) : kind.touchesMemory = true := by
  obtain ⟨reads, writes, _, _⟩ := intent
  cases reads <;> cases writes <;> simp [kindOf] at h <;> subst h <;> rfl

/--
Build the certified event recording that `d` was performed with `outcome`.

`none` exactly when the outcome committed nothing — a denial, or an inert intent
the descriptor's own well-formedness already forbids. A denial emits a violation,
not an event: nothing happened to any byte.

The well-formedness proof is discharged here, from the `Committed` fields, so a
caller going through this function never assembles one and never has an
opportunity to skip it.

**The only producer, now by construction.** `ValidMemoryEvent.mk` is private, so
no caller outside `Grass/Memory/Event.lean` can assemble one, and this is the only
declaration inside it that returns one. A probe confirms the direct assembly is a
compile error rather than a discouraged habit.

That claim was withdrawn once and is restored deliberately. The constructor was
public, review assembled an event whose status disagreed with its own counts, and
the honest response at the time was to weaken the claim rather than defend it.
Sealing is the fix that makes the strong version true.

Sealing is not sufficient on its own and should not be read as if it were. It
stops an event bypassing the fields; it says nothing about whether the fields are
strong enough. Two of them were not being compared at all until that same review,
which is what `statusAgreesWithReads` and `statusAgreesWithWrites` fixed. The
fields remain the thing to keep honest.
-/
def ofOutcome (id : EventId) (contextKind : ContextKind) (cause : EventCause)
    (space : AddressSpace) (d : AccessDescriptor) (outcome : AccessOutcome d) :
    Option ValidMemoryEvent :=
  if hspace : space.id ≠ d.provenance.space then Option.none else
  match houtcome : outcome.committed? with
  | Option.none => Option.none
  | some c =>
      match hkind : kindOf d.intent with
      | Option.none => Option.none
      | some kind =>
          some
            { event :=
                { id := id
                  context := { id := d.context, kind := contextKind }
                  cause := cause
                  space := space
                  provenance := d.provenance
                  range := d.range
                  kind := kind
                  valueRead := c.observed
                  valueWritten := c.written
                  ordering := d.ordering
                  status := outcome.status
                  readCommitted := c.readCount
                  writeCommitted := c.writeCount }
              wellFormed :=
                { spaceAgreesWithProvenance := by simpa using hspace
                  readValuePresent := fun h =>
                    c.observedPresent (by rw [← reads_kindOf hkind]; exact h)
                  readValueAbsent := fun h =>
                    c.observedAbsent (by rw [← reads_kindOf hkind]; exact h)
                  writeValuePresent := fun h =>
                    c.writtenPresent (by rw [← writes_kindOf hkind]; exact h)
                  writeValueAbsent := fun h =>
                    c.writtenAbsent (by rw [← writes_kindOf hkind]; exact h)
                  noLocationWhenUntouched := fun hu =>
                    absurd (touchesMemory_kindOf hkind) (by rw [hu]; simp)
                  writtenLength := fun bytes hb => by
                    have hb' : c.written = some bytes := hb
                    have hcount : c.writeCount = bytes.length := by
                      simp [Committed.writeCount, hb']
                    have hfit := c.writtenFits bytes hb'
                    show bytes.length = (d.range.take c.writeCount).size
                    rw [ByteRange.take_size, hcount]
                    omega
                  readLength := fun bytes hb => by
                    have hb' : c.observed = some bytes := hb
                    have hcount : c.readCount = bytes.length := by
                      simp [Committed.readCount, hb']
                    have hfit := c.observedFits bytes hb'
                    show bytes.length = (d.range.take c.readCount).size
                    rw [ByteRange.take_size, hcount]
                    omega
                  readWithinRange := c.readCount_le
                  writeWithinRange := c.writeCount_le
                  statusWellFormed := outcome.status_wellFormed
                  statusAgreesWithReads := by
                    cases houtcome' : outcome with
                    | completed c' =>
                      subst houtcome'
                      simp only [AccessOutcome.committed?] at houtcome
                      cases Option.some.inj houtcome
                      rfl
                    | faulted f c' =>
                      subst houtcome'
                      simp only [AccessOutcome.committed?] at houtcome
                      cases Option.some.inj houtcome
                      rfl
                    | denied v =>
                      subst houtcome'
                      simp [AccessOutcome.committed?] at houtcome
                  statusAgreesWithWrites := by
                    cases houtcome' : outcome with
                    | completed c' =>
                      subst houtcome'
                      simp only [AccessOutcome.committed?] at houtcome
                      cases Option.some.inj houtcome
                      rfl
                    | faulted f c' =>
                      subst houtcome'
                      simp only [AccessOutcome.committed?] at houtcome
                      cases Option.some.inj houtcome
                      rfl
                    | denied v =>
                      subst houtcome'
                      simp [AccessOutcome.committed?] at houtcome } }

/--
**Every event this module can mint touches memory.**

The fact that makes `not_conflicts_of_untouched` and
`WellFormed.noLocationWhenUntouched` vacuous over any trace, stated so that the
vacuity is a theorem rather than something a reader has to reconstruct. It follows
from `kindOf`'s three cases and is what `ofOutcome` itself relies on to discharge
`kindTouchesMemory`.

If §7.1's `fence` kind ever becomes constructible, this theorem is what breaks, which
is the right place for the breakage to appear.
-/
theorem touchesMemory_ofOutcome {id : EventId} {contextKind : ContextKind}
    {cause : EventCause} {space : AddressSpace} {d : AccessDescriptor}
    {outcome : AccessOutcome d} {valid : ValidMemoryEvent}
    (h : ofOutcome id contextKind cause space d outcome = some valid) :
    valid.event.kind.touchesMemory = true := by
  unfold ofOutcome at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  next c _ =>
    split at h
    · exact absurd h (by simp)
    · next kind hkind =>
      injection h with h
      subst h
      exact touchesMemory_kindOf hkind

/-- The event an access produces records exactly the access's own range. -/
@[simp] theorem range_of_ofOutcome {id : EventId} {contextKind : ContextKind}
    {cause : EventCause} {space : AddressSpace} {d : AccessDescriptor}
    {outcome : AccessOutcome d} {valid : ValidMemoryEvent}
    (h : ofOutcome id contextKind cause space d outcome = some valid) :
    valid.event.range = d.range := by
  unfold ofOutcome at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  cases h
  rfl

/-- A denied outcome produces no event. Nothing was touched, so nothing is
recorded in the trace; the violation ledger is where a denial appears. -/
@[simp] theorem ofOutcome_denied (id : EventId) (contextKind : ContextKind)
    (cause : EventCause) (space : AddressSpace) (d : AccessDescriptor)
    (violation : AuditViolation) :
    ofOutcome id contextKind cause space d (.denied violation) = Option.none := by
  unfold ofOutcome
  simp

end MemoryEvent

end Grass.Memory
