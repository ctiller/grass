import Grass.Memory.Event

/-!
# Every clause of the event seal, refused

`MemoryEvent.WellFormed` is the seal on every event that enters
`MachineState.events`. It has eleven clauses and, until this file, **nothing in the
tree depended on any of them holding**.

Review swept it: each clause's proposition replaced by `True`, with `ofOutcome`'s
construction of it co-edited to `trivial` so that the sole producer's own proof is not
what is being tested. Thirteen builds, thirteen green — the seal had thirteen clauses
then. That is the same result round eighteen recorded for
`AccessDescriptor.WellFormedIn` — twelve of fourteen — on the sibling seal no round had
read.

**Two mechanisms had to change before this file could exist.** The structure had no
`Decidable` instance, so no fixture could name one of its clauses; it has one now, and
every conjunct is a field in declaration order, so a clause added later is a type error
there rather than a silently unchecked seal. And `Tools/ConsultedAudit.py` skipped any
structure whose name ends `WellFormed`, on the argument that a proof obligation's
purpose is that a constructor had to discharge it — which this module's own
`touchesMemory_ofOutcome` disproves, since no event `ofOutcome` can mint fails
`noLocationWhenUntouched` and discharging it therefore proves nothing about it.
`AccessDescriptor.WellFormedIn` was only ever in scope because its name does not end
that way.

**The pairing, and the two ways this file has already got it wrong.** A refusal alone
would not distinguish "this clause caught it" from "some other clause did", so each
neighbour must fail **exactly one clause** — which `sealClauses` decides and
`each_neighbour_fails_exactly_one_clause` asserts, so the property is checked rather
than argued.

The first version said "where a neighbour is more than one *field* from the baseline,
it carries its own control". That is the wrong quantifier: the failure mode is over
clauses, and a one-field neighbour is two clauses from the baseline whenever two
clauses read one field. Five of thirteen neighbours were failing two or three clauses
each, under a commit message asserting all thirteen were caught.

The second version added `each_neighbour_fails_exactly_one_clause` — and wrote its
entries as **fresh event terms** rather than over the neighbours the theorems above
state. So for two clauses it decided a repaired event the file did not contain, for two
more it decided nothing at all, and the commit message described repairs that were
never applied. An index that does not name the same terms as the thing it indexes is
not an index. Every neighbour is a `def` now, and both the refusal theorem and the
index entry are stated over that one name, so the two cannot drift.

**Two clauses are gone**, and that is the other thing the sweep found.
`readWithinRange` and `writeWithinRange` could not be isolated by any event:
`statusAgreesWithReads` ties the count to the status and `statusWellFormed` bounds the
status, so nothing can fail one without failing the others. They were implied, exactly
as `PreservationLaws`' sixth conjunct was, and `MemoryEvent.readCommitted_le_size` and
`MemoryEvent.writeCommitted_le_size` state what they said.
-/

namespace Tests.Memory.EventClauses

open Grass.Core Grass.Memory

private def events : FreshSupply EventTag := .initial
private def allocs : FreshSupply AllocTag := .initial
private def contexts : FreshSupply ContextTag := .initial
private def epochs : FreshSupply EpochTag := .initial

/-- The storage the event touches. -/
def buffer : AllocId := allocs.fresh.1

/-- The context that ran it. -/
def thread : ContextId := contexts.fresh.1

private def epoch : EpochId := epochs.fresh.1

/-- Provenance of the whole buffer. -/
def prov : Provenance :=
  { space := .cpuVirtual, root := buffer, epoch := epoch, source := .virtualAlloc
    rootExtent := ⟨0, 64⟩, path := [] }

/-- The device space this fixture uses, so the clause about space agreement has a real
second space to disagree with rather than an invented one. -/
def deviceHostVisible64 : AddressSpace :=
  { id := .deviceHostVisible, repr := .numeric 64, memoryType := .notHostCached
    coherence := .requiresExplicitVisibility }

/--
Which clauses of the seal an event fails, by name.

**The standing check, and the thing this file was missing.** Every theorem below says
an event is refused; none of them could say *which clause refused it*, so five
neighbours failed two or three clauses each while their docstrings named one, and a
commit message said all thirteen were caught. `sealClauses` decides it, and
`each_neighbour_fails_exactly_one_clause` asserts the property the file's argument
rests on.

The clause propositions are restated here rather than projected, because a field of a
`Prop` structure cannot be projected from a value that does not satisfy it. That is a
second source of truth, and the commit that added it argued the risk away — "if the two
drift the theorem below stops matching the `Decidable` instance and fails" — which is
an argument and not a check, in a file whose whole subject is the difference.

`sealClauses_is_the_seal` is the check. It says this function returns the empty list on
exactly the events the seal admits, so no drift in any clause proposition can survive:
weaken one here and the forward direction stops proving; weaken one in the structure
and the reverse direction does. What it does *not* say is that each name labels the
clause beside it — two labels could be exchanged and both theorems would still hold —
so the names are written in declaration order and read against the structure by eye.
-/
def sealClauses (e : MemoryEvent) : List String :=
  (if e.kind.reads = true → e.valueRead.isSome then [] else ["readValuePresent"]) ++
  (if e.kind.reads = false → e.valueRead = Option.none then [] else ["readValueAbsent"]) ++
  (if e.kind.writes = true → e.valueWritten.isSome then [] else ["writeValuePresent"]) ++
  (if e.kind.writes = false → e.valueWritten = Option.none then []
   else ["writeValueAbsent"]) ++
  (if e.kind.touchesMemory = false → e.range.IsEmpty then []
   else ["noLocationWhenUntouched"]) ++
  (if ∀ bytes ∈ e.valueWritten, bytes.length = e.committedWriteRange.size then []
   else ["writtenLength"]) ++
  (if ∀ bytes ∈ e.valueRead, bytes.length = e.committedReadRange.size then []
   else ["readLength"]) ++
  (if e.status.WellFormed e.range.size then [] else ["statusWellFormed"]) ++
  (if e.status.committedReads = e.readCommitted then [] else ["statusAgreesWithReads"]) ++
  (if e.status.committedWrites = e.writeCommitted then []
   else ["statusAgreesWithWrites"]) ++
  (if e.space.id = e.provenance.space then [] else ["spaceAgreesWithProvenance"])

/-! ## The four well-formed events every neighbour is measured against -/

/-- **The baseline: a completed eight-byte write.** -/
def store : MemoryEvent :=
  { id := events.fresh.1
    context := { id := thread, kind := .thread }
    cause := ⟨⟨"fixture"⟩⟩
    space := AddressSpace.cpuVirtual64
    provenance := prov, range := ⟨0, 8⟩, kind := .write
    valueRead := Option.none, valueWritten := some (List.replicate 8 0xAB)
    ordering := .plain, status := .completed 0 8
    readCommitted := 0, writeCommitted := 8 }

/-- The reading baseline. A read of zero bytes carrying nothing is a different event,
so the counts move with the kind and the neighbours about reading are measured against
this rather than against `store`. -/
def readStore : MemoryEvent :=
  { store with
    kind := .read, valueRead := some (List.replicate 8 0xAB)
    valueWritten := Option.none, status := .completed 8 0
    readCommitted := 8, writeCommitted := 0 }

/-- The fence baseline, for the two clauses about an event that touches no memory. -/
def fence : MemoryEvent :=
  { store with
    kind := .fence, range := ByteRange.empty 0, valueWritten := Option.none
    status := .completed 0 0, writeCommitted := 0 }

/-- The control baseline. `noLocationWhenUntouched`'s docstring names *two* kinds --
"a fence or control event has no location" -- and every fixture in this file was a
fence, so review narrowed the clause's guard from `touchesMemory = false` to
`kind = .fence`, co-editing the `Decidable` instance, `sealClauses` and `ofOutcome`'s
discharge, and the whole tree stayed green with a control event carrying an eight-byte
range admitted by the seal.

`EventKind.control` is minted nowhere else in the tree, which is why it was the half
with no fixture and why it was in `Tools/ReachabilityAudit.py`'s allowlist. Its twin
left that allowlist a round earlier for exactly the reason this file now mints one. -/
def control : MemoryEvent := { fence with kind := .control }

/-! ## The eleven neighbours, one per clause

Each is one `def`, named for the clause it isolates, and each is used twice below: once
by the theorem that says the seal refuses it, and once by the index that says *which*
clause did. Writing the index over fresh terms instead is the defect this shape exists
to prevent. -/

/-- `readValuePresent`: a reading event with no observed bytes. -/
def readValuePresentNeighbour : MemoryEvent :=
  { readStore with valueRead := Option.none }

/-- `readValueAbsent`: a non-reading event carrying observed bytes.

The value is *empty* rather than eight bytes, and that is the whole difference between
this neighbour and one that proves nothing: `store` reads zero, so its committed read
range is empty and an eight-byte value fails `readLength` as well. One field from the
baseline, two clauses from it. -/
def readValueAbsentNeighbour : MemoryEvent := { store with valueRead := some [] }

/-- `writeValuePresent`: a writing event with no written bytes. -/
def writeValuePresentNeighbour : MemoryEvent :=
  { store with valueWritten := Option.none }

/-- `writeValueAbsent`: a non-writing event carrying written bytes. Empty for the same
reason as `readValueAbsentNeighbour`: the fence's committed write range is empty, so
`writtenLength` would fail too on any longer value. -/
def writeValueAbsentNeighbour : MemoryEvent := { fence with valueWritten := some [] }

/-- `noLocationWhenUntouched`: a fence with a location. One field from `fence`. -/
def noLocationWhenUntouchedNeighbour : MemoryEvent := { fence with range := ⟨0, 8⟩ }

/-- `noLocationWhenUntouched` again, for the other kind the clause names. One field
from `control`, and the neighbour whose absence let the clause be narrowed to one
kind. -/
def noLocationWhenUntouchedControlNeighbour : MemoryEvent :=
  { control with range := ⟨0, 8⟩ }

/-- `writtenLength`: written bytes numbering less than the committed write range says.
This is what connects `docs/MEMORY_MODEL.md` §4's "a write initializes only the bytes
it actually completes" to the event record. -/
def writtenLengthNeighbour : MemoryEvent :=
  { store with valueWritten := some (List.replicate 4 0xAB) }

/-- `readLength`: the same for observed bytes, against `readStore`. -/
def readLengthNeighbour : MemoryEvent :=
  { readStore with valueRead := some (List.replicate 4 0xAB) }

/-- `statusWellFormed`: neither the status nor, through it, the event's own counts
exceed the range.

The written value stays at eight bytes rather than growing with the count, because
`committedWriteRange` is `range.take writeCommitted` and `take` is capped by the range
— so a sixteen-byte value would fail `writtenLength` as well and this neighbour would
prove nothing. There were two further clauses bounding `readCommitted` and
`writeCommitted` directly; no event can fail either without failing this one, which is
why they are gone and `MemoryEvent.readCommitted_le_size` states what they said. -/
def statusWellFormedNeighbour : MemoryEvent :=
  { store with status := .completed 0 16, writeCommitted := 16 }

/-- `statusAgreesWithReads`: the status and the counts are the same two facts. Review
built an event whose status said it observed nothing while `readCommitted` said eight,
discharged every other clause by `decide`, and wrapped it in a `ValidMemoryEvent`. -/
def statusAgreesWithReadsNeighbour : MemoryEvent :=
  { store with status := .completed 4 8 }

/-- `statusAgreesWithWrites`: the write half. -/
def statusAgreesWithWritesNeighbour : MemoryEvent :=
  { store with status := .completed 0 4 }

/-- `spaceAgreesWithProvenance`: the event's address space is the one its provenance
names. Two records of one fact, which agreed only because `performAccess` resolves the
space through the profile's table before calling `ofOutcome`. -/
def spaceAgreesWithProvenanceNeighbour : MemoryEvent :=
  { store with space := deviceHostVisible64 }

/-! ## The seal refuses every one of them

Without the four controls, every refusal here would be compatible with "this event was
malformed for some other reason". -/

/-- The baseline is well formed. -/
theorem the_baseline_is_well_formed : store.WellFormed := by decide

/-- So is the reading baseline. -/
theorem the_reading_baseline_is_well_formed : readStore.WellFormed := by decide

/-- So is the fence. -/
theorem the_fence_is_well_formed : fence.WellFormed := by decide

/-- So is the control event. -/
theorem the_control_event_is_well_formed : control.WellFormed := by decide

/-- A reading event carries the bytes it observed. -/
theorem a_read_without_bytes_is_refused : ¬ readValuePresentNeighbour.WellFormed := by
  decide

/-- A non-reading event carries no observed bytes. -/
theorem a_non_reading_event_with_bytes_is_refused :
    ¬ readValueAbsentNeighbour.WellFormed := by decide

/-- A writing event carries the bytes it wrote. -/
theorem a_write_without_bytes_is_refused :
    ¬ writeValuePresentNeighbour.WellFormed := by decide

/-- A non-writing event carries no written bytes. -/
theorem a_non_writing_event_with_bytes_is_refused :
    ¬ writeValueAbsentNeighbour.WellFormed := by decide

/-- A fence or control event has no location, so its range is empty. -/
theorem a_fence_with_a_location_is_refused :
    ¬ noLocationWhenUntouchedNeighbour.WellFormed := by decide

/-- And the control half of the same sentence. -/
theorem a_control_event_with_a_location_is_refused :
    ¬ noLocationWhenUntouchedControlNeighbour.WellFormed := by decide

/-- Written bytes number exactly what the committed write range says. -/
theorem a_short_written_value_is_refused : ¬ writtenLengthNeighbour.WellFormed := by
  decide

/-- Observed bytes number exactly what the committed read range says. -/
theorem a_short_observed_value_is_refused : ¬ readLengthNeighbour.WellFormed := by
  decide

/-- The status does not claim more bytes than the range covers. -/
theorem a_status_claiming_more_than_the_range_is_refused :
    ¬ statusWellFormedNeighbour.WellFormed := by decide

/-- The status agrees with the event's own read count. -/
theorem a_status_disagreeing_about_reads_is_refused :
    ¬ statusAgreesWithReadsNeighbour.WellFormed := by decide

/-- And with its write count. -/
theorem a_status_disagreeing_about_writes_is_refused :
    ¬ statusAgreesWithWritesNeighbour.WellFormed := by decide

/-- The event's address space is the one its provenance names. -/
theorem a_space_disagreeing_with_the_provenance_is_refused :
    ¬ spaceAgreesWithProvenanceNeighbour.WellFormed := by decide

/-- **Every neighbour fails exactly the clause it names, and all four controls fail
none.**

This is the theorem the file's argument rests on. Each refusal above says an event is
not well formed; only this says *which clause* refused it, and without it five of the
neighbours were failing two or three clauses each while their docstrings named one.
Round eighteen found the same thing in the sibling seal by hand; here it is decided.

Read it as the file's index: left to right, the four controls and then the eleven
clauses in declaration order, each with the neighbour that isolates it — twelve
neighbours for eleven clauses, because `noLocationWhenUntouched` names two event kinds
and one fixture decides one of them. The entries
name the same `def`s the theorems above do, which the first version of this theorem did
not — it wrote fresh terms, so it could pass while the file it indexed said something
else. -/
theorem each_neighbour_fails_exactly_one_clause :
    sealClauses store = [] ∧
    sealClauses readStore = [] ∧
    sealClauses fence = [] ∧
    sealClauses control = [] ∧
    sealClauses readValuePresentNeighbour = ["readValuePresent"] ∧
    sealClauses readValueAbsentNeighbour = ["readValueAbsent"] ∧
    sealClauses writeValuePresentNeighbour = ["writeValuePresent"] ∧
    sealClauses writeValueAbsentNeighbour = ["writeValueAbsent"] ∧
    sealClauses noLocationWhenUntouchedNeighbour = ["noLocationWhenUntouched"] ∧
    sealClauses noLocationWhenUntouchedControlNeighbour = ["noLocationWhenUntouched"] ∧
    sealClauses writtenLengthNeighbour = ["writtenLength"] ∧
    sealClauses readLengthNeighbour = ["readLength"] ∧
    sealClauses statusWellFormedNeighbour = ["statusWellFormed"] ∧
    sealClauses statusAgreesWithReadsNeighbour = ["statusAgreesWithReads"] ∧
    sealClauses statusAgreesWithWritesNeighbour = ["statusAgreesWithWrites"] ∧
    sealClauses spaceAgreesWithProvenanceNeighbour = ["spaceAgreesWithProvenance"] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-- **This function is the seal, and not a paraphrase of it.**

`sealClauses` restates all eleven clause propositions, which is a second source of
truth: every fixture above is decided against *this* list, so a clause that drifted
from the structure would make the whole file agree with itself and say nothing about
the seal. This is that risk closed rather than argued about. An event fails no clause
here exactly when it satisfies `MemoryEvent.WellFormed`, so a weakening on either side
breaks one direction of the proof.

It does not fix the *labels*: exchanging two names would leave both directions
provable. The names are in declaration order, which is how the `Decidable` instance is
written too, and that much is read by eye. -/
theorem sealClauses_is_the_seal (e : MemoryEvent) : sealClauses e = [] ↔ e.WellFormed := by
  constructor
  · intro h
    simp only [sealClauses, List.append_eq_nil_iff, ite_eq_left_iff,
      List.cons_ne_nil, imp_false, Decidable.not_not] at h
    exact ⟨h.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2,
      h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
      h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · intro w
    simp only [sealClauses, List.append_eq_nil_iff, ite_eq_left_iff,
      List.cons_ne_nil, imp_false, Decidable.not_not]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w.readValuePresent, w.readValueAbsent⟩, w.writeValuePresent⟩,
      w.writeValueAbsent⟩, w.noLocationWhenUntouched⟩, w.writtenLength⟩,
      w.readLength⟩, w.statusWellFormed⟩, w.statusAgreesWithReads⟩,
      w.statusAgreesWithWrites⟩, w.spaceAgreesWithProvenance⟩

end Tests.Memory.EventClauses
