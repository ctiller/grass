import Grass.Memory.Event

/-!
# Every clause of the event seal, refused

`MemoryEvent.WellFormed` is the seal on every event that enters
`MachineState.events`. It has thirteen clauses and, until this file, **nothing in the
tree depended on any of them holding**.

Review swept it: each clause's proposition replaced by `True`, with `ofOutcome`'s
construction of it co-edited to `trivial` so that the sole producer's own proof is not
what is being tested. Thirteen builds, thirteen green. That is the same result round
eighteen recorded for `AccessDescriptor.WellFormedIn` — twelve of fourteen — on the
sibling seal no round had read.

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

**The pairing.** A refusal alone would not distinguish "this clause caught it" from
"some other clause did", so the baseline is proved well formed in the same theorem.
Where a neighbour is more than one field from the baseline — because two clauses read
one field, or because a count and its status must move together — it carries its own
control, and says so. That rule is the one round eighteen found broken three times in
the sibling file.
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

/-- The device space this fixture uses, so the clause above has a real second space to
disagree with rather than an invented one. -/
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
second source of truth, and the commit that added it argued the risk away -- "if the
two drift the theorem below stops matching the `Decidable` instance and fails" -- which
is an argument and not a check, in a file whose whole subject is the difference.

`sealClauses_is_the_seal` is the check. It says this function returns the empty list on
exactly the events the seal admits, so no drift in any clause proposition can survive:
weaken one here and the forward direction stops proving; weaken one in the structure
and the reverse direction does. What it does *not* say is that each name labels the
clause beside it -- two labels could be exchanged and both theorems would still hold --
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

/-- **The baseline: a completed eight-byte write.** Every theorem below differs from
this in one field, or says why it differs in more. -/
def store : MemoryEvent :=
  { id := events.fresh.1
    context := { id := thread, kind := .thread }
    cause := ⟨⟨"fixture"⟩⟩
    space := AddressSpace.cpuVirtual64
    provenance := prov, range := ⟨0, 8⟩, kind := .write
    valueRead := Option.none, valueWritten := some (List.replicate 8 0xAB)
    ordering := .plain, status := .completed 0 8
    readCommitted := 0, writeCommitted := 8 }

/-- The baseline is well formed. Without this every refusal below would be compatible
with "this event was malformed for some other reason". -/
theorem the_baseline_is_well_formed : store.WellFormed := by decide

/-- `readValuePresent`: a reading event carries the bytes it observed. The read
counts move with the kind, because a read of zero bytes carrying nothing is a
different event; `the_reading_baseline_is_well_formed` is the control. -/
theorem a_read_without_bytes_is_refused :
    ¬ ({ store with
          kind := .read, valueWritten := Option.none,
          status := .completed 8 0, readCommitted := 8,
          writeCommitted := 0 } : MemoryEvent).WellFormed := by decide

/-- The control: the same event carrying what it read. -/
theorem the_reading_baseline_is_well_formed :
    ({ store with
          kind := .read, valueRead := some (List.replicate 8 0xAB),
          valueWritten := Option.none, status := .completed 8 0,
          readCommitted := 8, writeCommitted := 0 } :
      MemoryEvent).WellFormed := by decide

/-- `readValueAbsent`: a non-reading event carries no observed bytes. One field from
the baseline, which writes and reads nothing. -/
theorem a_non_reading_event_with_bytes_is_refused :
    ¬ ({ store with valueRead := some (List.replicate 8 0xAB) } :
      MemoryEvent).WellFormed := by decide

/-- `writeValuePresent`: a writing event carries the bytes it wrote. -/
theorem a_write_without_bytes_is_refused :
    ¬ ({ store with
          valueWritten := Option.none } : MemoryEvent).WellFormed := by decide

/-- `writeValueAbsent`: a non-writing event carries no written bytes. The fence
carries the baseline's written bytes; `the_fence_is_well_formed` is the control, and
the two differ in `valueWritten` alone. -/
theorem a_non_writing_event_with_bytes_is_refused :
    ¬ ({ store with
          kind := .fence, range := ByteRange.empty 0,
          status := .completed 0 0, writeCommitted := 0 } : MemoryEvent).WellFormed := by
  decide

/-- The control for it, and for `noLocationWhenUntouched` below. -/
theorem the_fence_is_well_formed :
    ({ store with
          kind := .fence, range := ByteRange.empty 0,
          valueWritten := Option.none, status := .completed 0 0,
          writeCommitted := 0 } : MemoryEvent).WellFormed := by decide

/-- `noLocationWhenUntouched`: a fence or control event has no location, so its range
is empty. One field from `the_fence_is_well_formed`. -/
theorem a_fence_with_a_location_is_refused :
    ¬ ({ store with
          kind := .fence, valueWritten := Option.none,
          status := .completed 0 0, writeCommitted := 0 } : MemoryEvent).WellFormed := by
  decide

/-- `writtenLength`: written bytes number exactly what the committed write range says.
This is what connects `docs/MEMORY_MODEL.md` §4's "a write initializes only the bytes
it actually completes" to the event record. -/
theorem a_short_written_value_is_refused :
    ¬ ({ store with valueWritten := some (List.replicate 4 0xAB) } :
      MemoryEvent).WellFormed := by decide

/-- `readLength`: the same for observed bytes, against
`the_reading_baseline_is_well_formed`. -/
theorem a_short_observed_value_is_refused :
    ¬ ({ store with
          kind := .read, valueRead := some (List.replicate 4 0xAB),
          valueWritten := Option.none, status := .completed 8 0,
          readCommitted := 8, writeCommitted := 0 } : MemoryEvent).WellFormed := by
  decide

/-- `readWithinRange`: neither count exceeds the range. The status moves with the
count, because `statusAgreesWithReads` ties them; the discriminating difference from
`the_reading_baseline_is_well_formed` is that sixteen exceeds eight. -/
theorem a_read_count_past_the_range_is_refused :
    ¬ ({ store with
          kind := .read, valueRead := some (List.replicate 16 0xAB),
          valueWritten := Option.none, status := .completed 16 0,
          readCommitted := 16, writeCommitted := 0 } : MemoryEvent).WellFormed := by
  decide

/-- `writeWithinRange`: the write half. -/
theorem a_write_count_past_the_range_is_refused :
    ¬ ({ store with
          valueWritten := some (List.replicate 16 0xAB),
          status := .completed 0 16, writeCommitted := 16 } : MemoryEvent).WellFormed := by
  decide

/-- `statusWellFormed`: the status does not claim more bytes than the range covers.
Distinct from the two clauses above, which bound the event's *own* counts: this bounds
the status, and a partial commit is where the two can disagree. -/
theorem a_status_claiming_more_than_the_range_is_refused :
    ¬ ({ store with
          status := .completed 0 16, writeCommitted := 16,
          valueWritten := some (List.replicate 8 0xAB) } :
      MemoryEvent).WellFormed := by decide

/-- `statusAgreesWithReads`: the status and the counts are the same two facts. Review
built an event whose status said it observed nothing while `readCommitted` said eight,
discharged every other clause by `decide`, and wrapped it in a `ValidMemoryEvent`. -/
theorem a_status_disagreeing_about_reads_is_refused :
    ¬ ({ store with
          status := .completed 4 8 } : MemoryEvent).WellFormed := by decide

/-- `statusAgreesWithWrites`: the write half. -/
theorem a_status_disagreeing_about_writes_is_refused :
    ¬ ({ store with
          status := .completed 0 4 } : MemoryEvent).WellFormed := by decide

/-- `spaceAgreesWithProvenance`: the event's address space is the one its provenance
names. Two records of one fact, which agreed only because `performAccess` resolves the
space through the profile's table before calling `ofOutcome`. -/
theorem a_space_disagreeing_with_the_provenance_is_refused :
    ¬ ({ store with
          space := deviceHostVisible64 } : MemoryEvent).WellFormed := by
  decide

/-- **Every neighbour fails exactly the clause it names, and both controls fail none.**

This is the theorem the file's argument rests on and did not have. Each refusal above
says an event is not well formed; only this says *which clause* refused it, and without
it five of the neighbours were failing two or three clauses each while their docstrings
named one. Round eighteen found the same thing in the sibling seal by hand; here it is
decided.

Read it as the file's index: left to right, the eleven clauses in declaration order,
each with the neighbour that isolates it. -/
theorem each_neighbour_fails_exactly_one_clause :
    sealClauses store = [] ∧
    sealClauses ({ store with
      kind := .read, valueWritten := Option.none, status := .completed 8 0,
      readCommitted := 8, writeCommitted := 0 }) = ["readValuePresent"] ∧
    sealClauses ({ store with valueRead := some [] }) = ["readValueAbsent"] ∧
    sealClauses ({ store with valueWritten := Option.none }) = ["writeValuePresent"] ∧
    sealClauses ({ store with
      kind := .fence, range := ByteRange.empty 0, valueWritten := some [],
      status := .completed 0 0, writeCommitted := 0 }) = ["writeValueAbsent"] ∧
    sealClauses ({ store with
      kind := .fence, valueWritten := Option.none, status := .completed 0 0,
      writeCommitted := 0 }) = ["noLocationWhenUntouched"] ∧
    sealClauses ({ store with valueWritten := some (List.replicate 4 0xAB) }) =
      ["writtenLength"] ∧
    sealClauses ({ store with
      kind := .read, valueRead := some (List.replicate 4 0xAB),
      valueWritten := Option.none, status := .completed 8 0,
      readCommitted := 8, writeCommitted := 0 }) = ["readLength"] ∧
    sealClauses ({ store with
      status := .completed 0 16, writeCommitted := 16,
      valueWritten := some (List.replicate 8 0xAB) }) = ["statusWellFormed"] ∧
    sealClauses ({ store with status := .completed 4 8 }) = ["statusAgreesWithReads"] ∧
    sealClauses ({ store with status := .completed 0 4 }) = ["statusAgreesWithWrites"] ∧
    sealClauses ({ store with space := deviceHostVisible64 }) =
      ["spaceAgreesWithProvenance"] ∧
    sealClauses ({ store with
      kind := .read, valueRead := some (List.replicate 8 0xAB),
      valueWritten := Option.none, status := .completed 8 0,
      readCommitted := 8, writeCommitted := 0 }) = [] ∧
    sealClauses ({ store with
      kind := .fence, range := ByteRange.empty 0, valueWritten := Option.none,
      status := .completed 0 0, writeCommitted := 0 }) = [] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

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
