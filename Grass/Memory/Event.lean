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
deriving DecidableEq, Repr

namespace MemoryEvent

/-- The bytes this event actually committed, as a range. -/
def committedRange (e : MemoryEvent) : ByteRange :=
  e.range.take (e.status.committedBytes e.range.size)

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
    ∀ bytes, e.valueWritten = some bytes → bytes.length = e.committedRange.size
  /-- Observed bytes number exactly what the status says completed. -/
  readLength :
    ∀ bytes, e.valueRead = some bytes → bytes.length = e.committedRange.size
  /-- The status does not claim more bytes than the range covers. -/
  statusWellFormed : e.status.WellFormed e.range.size

/--
`Conflicts a b` holds when two events contend for the same bytes.

`docs/MEMORY_MODEL.md` §7.3: overlapping live ranges in the same storage, at
least one writing, and not both atomic. Note carefully what this is *not*: a
conflict is not a data race. A race additionally requires the two events to be
unordered by happens-before, which needs the consistency graph of M8. Two
conflicting events properly ordered by a lock are not a race.

Overlap is checked on the *committed* ranges, since bytes an event did not commit
are bytes it did not touch, and on `SameStorage`, since equal offsets in
different allocations are different bytes.
-/
def Conflicts (a b : MemoryEvent) : Prop :=
  a.kind.touchesMemory = true ∧ b.kind.touchesMemory = true ∧
  a.provenance.SameStorage b.provenance ∧
  a.committedRange.Overlaps b.committedRange ∧
  (a.kind.writes = true ∨ b.kind.writes = true) ∧
  ¬ (a.ordering.atomicity = .atomic ∧ b.ordering.atomicity = .atomic)

theorem Conflicts.symm {a b : MemoryEvent} (h : a.Conflicts b) : b.Conflicts a := by
  obtain ⟨ha, hb, hs, ho, hw, hat⟩ := h
  refine ⟨hb, ha, hs.symm, ?_, hw.symm, fun hc => hat ⟨hc.2, hc.1⟩⟩
  obtain ⟨offset, h₁, h₂⟩ := ho
  exact ⟨offset, h₂, h₁⟩

/-- Two reads never conflict, whatever their ordering. -/
theorem not_conflicts_of_both_read {a b : MemoryEvent}
    (ha : a.kind = .read) (hb : b.kind = .read) : ¬ a.Conflicts b := by
  rintro ⟨_, _, _, _, hw, _⟩
  rw [ha, hb] at hw
  simp [EventKind.writes] at hw

/-- Events in different storage never conflict, however their offsets compare.
This is `docs/MEMORY_MODEL.md` §7.5 at the event layer. -/
theorem not_conflicts_of_not_sameStorage {a b : MemoryEvent}
    (h : ¬ a.provenance.SameStorage b.provenance) : ¬ a.Conflicts b :=
  fun hc => h hc.2.2.1

/-- A fence conflicts with nothing, because it touches no bytes. -/
theorem not_conflicts_fence_left {a b : MemoryEvent} (h : a.kind = .fence) :
    ¬ a.Conflicts b := by
  rintro ⟨ht, _⟩
  rw [h] at ht
  simp [EventKind.touchesMemory] at ht

end MemoryEvent

/-!
## From a declared access to an event

An access declares what an operation *intends*; an event records what happened.
The bridge is what makes the vocabulary usable rather than decorative: an ISA
author declares accesses, and M2's `applyAccess` turns each performed access into
an event without either side inventing a second notion of what was touched.
-/

/--
The event kind an intent gives rise to, if any.

`none` for an inert intent, which reads, writes, and executes nothing. That case
is already rejected by `AccessDescriptor.WellFormed.notInert`; returning `none`
rather than picking a plausible kind keeps the rejection rather than papering
over it (`docs/FOUNDATION.md` law 8).

An instruction fetch maps to , because  reads. The
permission demand that distinguishes a fetch from a data read is carried by the
descriptor separately, not by the event kind.
-/
def AccessIntent.eventKind? (intent : AccessIntent) : Option EventKind :=
  if intent.reads && intent.writes then some .readModifyWrite
  else if intent.writes then some .write
  else if intent.reads then some .read
  else Option.none

@[simp] theorem AccessIntent.eventKind?_read : AccessIntent.read.eventKind? = some .read := rfl

@[simp] theorem AccessIntent.eventKind?_write :
    AccessIntent.write.eventKind? = some .write := rfl

@[simp] theorem AccessIntent.eventKind?_readWrite :
    AccessIntent.readWrite.eventKind? = some .readModifyWrite := rfl

/-- An inert intent yields no event, matching the descriptor's own rejection
of it. -/
theorem AccessIntent.eventKind?_eq_none_iff {intent : AccessIntent} :
    intent.eventKind? = Option.none ↔ intent.IsInert := by
  obtain ⟨reads, writes, _, _, _⟩ := intent
  cases reads <;> cases writes <;> simp [eventKind?, IsInert]

/-- The event kind reads exactly when the intent does. -/
theorem AccessIntent.reads_eventKind? {intent : AccessIntent} {kind : EventKind}
    (h : intent.eventKind? = some kind) : kind.reads = intent.reads := by
  obtain ⟨reads, writes, _, _, _⟩ := intent
  cases reads <;> cases writes <;> simp [eventKind?] at h <;> subst h <;> rfl

/-- The event kind writes exactly when the intent does. -/
theorem AccessIntent.writes_eventKind? {intent : AccessIntent} {kind : EventKind}
    (h : intent.eventKind? = some kind) : kind.writes = intent.writes := by
  obtain ⟨reads, writes, _, _, _⟩ := intent
  cases reads <;> cases writes <;> simp [eventKind?] at h <;> subst h <;> rfl

/-- Every event an access produces touches memory. An access is never a fence or
a control event; those arise from operations that declare no access at all. -/
theorem AccessIntent.touchesMemory_eventKind? {intent : AccessIntent} {kind : EventKind}
    (h : intent.eventKind? = some kind) : kind.touchesMemory = true := by
  obtain ⟨reads, writes, _, _, _⟩ := intent
  cases reads <;> cases writes <;> simp [eventKind?] at h <;> subst h <;> rfl

namespace MemoryEvent

/--
Build the event recording that `d` was performed with outcome `status`.

`none` exactly when the intent is inert, so an operation that declared it touches
nothing produces no event rather than an empty one.
-/
def ofAccess? (id : EventId) (contextKind : ContextKind) (cause : EventCause)
    (d : AccessDescriptor) (status : AccessStatus)
    (valueRead valueWritten : Option ByteSeq) : Option MemoryEvent :=
  (d.intent.eventKind?).map fun kind =>
    { id := id
      context := { id := d.context, kind := contextKind }
      cause := cause
      space := d.space
      provenance := d.provenance
      range := d.range
      kind := kind
      valueRead := valueRead
      valueWritten := valueWritten
      ordering := d.ordering
      status := status }

/-- The event an access produces records exactly the access's own range. Nothing
in the bridge widens or narrows what was touched. -/
@[simp] theorem range_of_ofAccess? {id : EventId} {contextKind : ContextKind}
    {cause : EventCause} {d : AccessDescriptor} {status : AccessStatus}
    {valueRead valueWritten : Option ByteSeq} {e : MemoryEvent}
    (h : ofAccess? id contextKind cause d status valueRead valueWritten = some e) :
    e.range = d.range := by
  simp only [ofAccess?, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-- The committed range of the event agrees with the committed range of the
access. This is what lets an initialization argument stated on the descriptor be
used on the event. -/
theorem committedRange_of_ofAccess? {id : EventId} {contextKind : ContextKind}
    {cause : EventCause} {d : AccessDescriptor} {status : AccessStatus}
    {valueRead valueWritten : Option ByteSeq} {e : MemoryEvent}
    (h : ofAccess? id contextKind cause d status valueRead valueWritten = some e) :
    e.committedRange = d.committedRange status := by
  simp only [ofAccess?, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/--
Event well-formedness follows from the values having the lengths the status
reports.

The payoff: an ISA author who declares a well-formed access and supplies values
of the committed length gets a well-formed event, rather than re-proving the
event conditions per instruction.
-/
theorem wellFormed_ofAccess? {id : EventId} {contextKind : ContextKind}
    {cause : EventCause} {d : AccessDescriptor} {status : AccessStatus}
    {valueRead valueWritten : Option ByteSeq} {e : MemoryEvent}
    (h : ofAccess? id contextKind cause d status valueRead valueWritten = some e)
    (readPresent : d.intent.reads = true → valueRead.isSome)
    (readAbsent : d.intent.reads = false → valueRead = Option.none)
    (writePresent : d.intent.writes = true → valueWritten.isSome)
    (writeAbsent : d.intent.writes = false → valueWritten = Option.none)
    (readLen : ∀ bytes, valueRead = some bytes →
      bytes.length = (d.committedRange status).size)
    (writeLen : ∀ bytes, valueWritten = some bytes →
      bytes.length = (d.committedRange status).size)
    (statusOk : status.WellFormed d.range.size) : e.WellFormed := by
  have hcommitted := committedRange_of_ofAccess? h
  simp only [ofAccess?, Option.map_eq_some_iff] at h
  obtain ⟨kind, hkind, rfl⟩ := h
  have hreads := AccessIntent.reads_eventKind? hkind
  have hwrites := AccessIntent.writes_eventKind? hkind
  have htouches := AccessIntent.touchesMemory_eventKind? hkind
  exact
    { readValuePresent := fun hr => readPresent (hreads ▸ hr)
      readValueAbsent := fun hr => readAbsent (hreads ▸ hr)
      writeValuePresent := fun hw => writePresent (hwrites ▸ hw)
      writeValueAbsent := fun hw => writeAbsent (hwrites ▸ hw)
      noLocationWhenUntouched := fun hu => absurd htouches (by rw [hu]; simp)
      writtenLength := fun bytes hb => hcommitted ▸ writeLen bytes hb
      readLength := fun bytes hb => hcommitted ▸ readLen bytes hb
      statusWellFormed := statusOk }

end MemoryEvent

end Grass.Memory
