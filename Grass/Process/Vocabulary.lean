/-!
# Process vocabulary and the event family

`docs/PROCESS.md` §2 gives a process four interface types — external events,
demands, a dependent result schema, and observations — and one event family
built over them.

## Why the fault, interruption, and violation types are carried too

`docs/PROCESS.md` §2 writes

```text
inductive ProcessEvent (v : ProcessVocabulary)
  | external (event : v.ExternalEvent)
  | result (demand : v.Demand) (result : v.Result demand)
  | interrupted (demand : v.Demand) (reason : InterruptReason)
  | fault (fault : LogicalFault)
  | environmentViolation (violation : EnvironmentViolation)
```

with the last three types unqualified, as though they were one fixed global
classification. This module carries them in `ProcessVocabulary` instead, so
they are `v.InterruptReason`, `v.LogicalFault`, and `v.EnvironmentViolation`.

The reason is `docs/PROCESS_SHARDING.md` §10, which lists "a closed
whole-program `ProcessKind`, `ProtocolKey`, or role sum" as a foundational
failure. A global `LogicalFault` is exactly that shape one level down: HTTP/2
error codes, Vulkan device-loss, zlib stream corruption, and a Win32 handle
violation are the fault classes of four unrelated subsystems, and no
enumeration owned by this layer can contain them without becoming the master
sum the sharding document forbids. `docs/FOUNDATION.md` law 8 then forbids the
escape hatch of an `| other (name : String)` constructor, because an
unclassified fault must be rejected rather than approximated.

Carrying them per vocabulary costs nothing at a child boundary, because a child
outcome already has to be routed to a parent event explicitly:
`docs/PROCESS.md` §3 requires `ChildDemandBinding.classify` to map *every*
child lifecycle outcome to a precise parent event. A translation between two
reason types is that map, not a new burden.

This is a deviation from the literal declaration in the normative document, and
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.6 records that it needs a
`docs/DECISIONS.md` entry.

It does move an obligation rather than remove one, and the move has to be
completed. With a single global classification, "the network may deliver an
environment violation to this process" is an obligation every process handles by
construction. With per-vocabulary classes, a process whose `EnvironmentViolation`
is `PEmpty` has made the corresponding `NetworkTransition.environmentViolation`
*unconstructible* rather than handled. That is sound only if the network
transition carries a total classification from the delivering side's classes into
the receiving vocabulary's, exactly as `ChildDemandBinding.classify` does at a
child boundary: an empty class is then a proof that the transition is
unreachable for this process, not a way to skip it.

That classification is `Grass/Process/Network/Transition.lean` and is scheduled
in M2. Until it exists, a `PEmpty` fault or violation class is an *assumption*
about the environment, not a discharged obligation, and this module says so
rather than implying otherwise.

## Why the event family is closed

The five constructors are closed on purpose, and that is not in tension with
the above. They are not a taxonomy of *what went wrong*; they are the complete
list of ways a process's state can be advanced from outside it: entropy arrived
(`external`), an outstanding demand was answered (`result`) or abandoned
(`interrupted`), the process itself failed (`fault`), or the environment broke a
contract the process was entitled to assume (`environmentViolation`). Adding a
sixth would mean a way to advance a process that no proof covers, which is what
`docs/PROCESS.md` §3 means by "no fabrication, bypass, or unclassified death is
possible".
-/

namespace Grass.Process

universe u

/--
The interface types of one process.

Everything here is what crosses the process boundary. Nothing here is a
realization fact: `docs/FOUNDATION.md` law 18 keeps occurrence identity,
batching, routing, and worker assignment out, and a `Demand` is therefore a
*value* describing an interaction, never a handle to a pending one.
-/
structure ProcessVocabulary : Type (u + 1) where
  /-- Entropy arriving from outside: a keystroke, a connection, a frame tick. -/
  ExternalEvent : Type u
  /-- An abstract interaction the process asks for. Not an occurrence. -/
  Demand : Type u
  /--
  The dependent schema of every permitted answer to a demand.

  Dependent rather than a single sum type because `docs/FOUNDATION.md` law 5
  requires every admitted result to be handled: a `WriteFile` demand's result
  type contains its byte count, and a `Sleep` demand's does not, so a proof
  cannot accidentally be discharged for the wrong demand's result space.
  -/
  Result : Demand → Type u
  /-- What the program's specification is entitled to observe. -/
  Observation : Type u
  /-- Why an outstanding demand was abandoned without a result. -/
  InterruptReason : Type u
  /-- How this process itself can fail. See the module note. -/
  LogicalFault : Type u
  /-- How the environment can break a contract this process assumed. -/
  EnvironmentViolation : Type u

namespace ProcessVocabulary

/--
The vocabulary of a process that claims it can never be interrupted, can never
fault, and will never be told its environment broke a contract.

Read the three `PEmpty` fields as assertions, not as omissions. They do not say
"this process has nothing to say about faults"; they say *no fault can occur*,
*no cancellation can arrive*, and *the environment never violates*. That is a
strong claim about the setting the process runs in, and the network transition
that would deliver such an event owes a proof that it cannot arise here. See the
module note.

`PEmpty` rather than `Unit` because the claim has to be enforced by
constructibility. With `Unit` an author could write a `Step` case for
`.fault ()` and a reviewer would have to read the body to find that it was
unreachable. `PEmpty` rather than `Empty` only because the vocabulary's fields
live in a general `Type u`.
-/
def quiescent (ExternalEvent Demand : Type u) (Result : Demand → Type u)
    (Observation : Type u) : ProcessVocabulary where
  ExternalEvent := ExternalEvent
  Demand := Demand
  Result := Result
  Observation := Observation
  InterruptReason := PEmpty
  LogicalFault := PEmpty
  EnvironmentViolation := PEmpty

end ProcessVocabulary

/--
The complete family of ways one process's state is advanced from outside it.

See the module note for why this family is closed while the fault classes it
carries are not.
-/
inductive ProcessEvent (v : ProcessVocabulary.{u}) : Type u
  /-- Entropy from outside the program. -/
  | external (event : v.ExternalEvent)
  /-- Exactly one outstanding demand was answered. -/
  | result (demand : v.Demand) (result : v.Result demand)
  /-- Exactly one outstanding demand was abandoned without a result. -/
  | interrupted (demand : v.Demand) (reason : v.InterruptReason)
  /-- The process itself failed. -/
  | fault (fault : v.LogicalFault)
  /-- The environment broke a contract the process was entitled to assume. -/
  | environmentViolation (violation : v.EnvironmentViolation)

namespace ProcessEvent

variable {v : ProcessVocabulary.{u}}

/--
The demand this event settles, if any.

`result` and `interrupted` are the two events that consume an outstanding
demand; the other three do not. `docs/PROCESS.md` §2 states the consequence:
"A result/interruption requires and consumes exactly one live matching item",
while an external event, fault, or violation leaves the outstanding bag alone.
`Grass/Process/Run.lean` is where that is enforced, and this function is what it
is enforced against, so that the correspondence is one definition rather than
five constructor cases restating it.
-/
def settles : ProcessEvent v → Option v.Demand
  | .external _ => none
  | .result demand _ => some demand
  | .interrupted demand _ => some demand
  | .fault _ => none
  | .environmentViolation _ => none

@[simp] theorem settles_external (event : v.ExternalEvent) :
    (ProcessEvent.external event).settles = none := rfl

@[simp] theorem settles_result (demand : v.Demand) (result : v.Result demand) :
    (ProcessEvent.result demand result).settles = some demand := rfl

@[simp] theorem settles_interrupted (demand : v.Demand)
    (reason : v.InterruptReason) :
    (ProcessEvent.interrupted demand reason).settles = some demand := rfl

@[simp] theorem settles_fault (fault : v.LogicalFault) :
    (ProcessEvent.fault fault).settles = none := rfl

@[simp] theorem settles_environmentViolation (violation : v.EnvironmentViolation) :
    (ProcessEvent.environmentViolation violation).settles = none := rfl

/--
The entropy this event carries, if it is entropy at all.

`settles` splits the family by whether an outstanding demand is consumed. This
splits it by a different question: did something outside the program happen?
Only `.external` did. A `.result` is the process's own request coming back, and
a `.fault` is the process failing — `docs/PROCESS.md` §2 lists them as separate
constructors for that reason.

`Grass/Process/Progress.lean` needs this second split and not the first: a
process that waits forever for entropy is legitimate, while one that faults in a
loop without emitting anything is the livelock a progress theorem exists to
exclude.
-/
def externalEntropy : ProcessEvent v → Option v.ExternalEvent
  | .external event => some event
  | .result _ _ => none
  | .interrupted _ _ => none
  | .fault _ => none
  | .environmentViolation _ => none

@[simp] theorem externalEntropy_external (event : v.ExternalEvent) :
    (ProcessEvent.external (v := v) event).externalEntropy = some event := rfl

@[simp] theorem externalEntropy_result (demand : v.Demand) (result : v.Result demand) :
    (ProcessEvent.result demand result).externalEntropy = none := rfl

@[simp] theorem externalEntropy_interrupted (demand : v.Demand)
    (reason : v.InterruptReason) :
    (ProcessEvent.interrupted demand reason).externalEntropy = none := rfl

@[simp] theorem externalEntropy_fault (fault : v.LogicalFault) :
    (ProcessEvent.fault fault).externalEntropy = none := rfl

@[simp] theorem externalEntropy_environmentViolation
    (violation : v.EnvironmentViolation) :
    (ProcessEvent.environmentViolation violation).externalEntropy = none := rfl

/-- Entropy settles nothing: it is not an answer to anything the process asked. -/
theorem settles_none_of_externalEntropy {event : ProcessEvent v}
    {entropy : v.ExternalEvent} (isEntropy : event.externalEntropy = some entropy) :
    event.settles = none := by
  cases event <;> simp_all [externalEntropy, settles]

end ProcessEvent

end Grass.Process
