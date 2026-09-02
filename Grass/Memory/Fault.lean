import Grass.Core.Name

/-!
# Architectural faults and completion status

`docs/MEMORY_MODEL.md` §8 draws a line this module depends on: an architectural
fault is a modeled event or transition, while an audit violation is a private
append-only diagnostic (`Grass/Memory/Audit.lean`). They are not two severities
of one thing. A fault is behavior the specification may permit; an audit
violation is behavior `VerifiedProgram` proves never occurs.

The other demand met here is §1's refusal to assume transactionality: "Grass must
not silently assume that a whole instruction is transactional." `AccessStatus`
therefore carries the number of bytes actually committed on a partial or faulting
access, and there is no constructor that means "faulted, so assume nothing
happened".
-/

namespace Grass.Memory

open Grass.Core

/--
The identity of an architectural fault class.

Open nominal, because the fault taxonomy belongs to the ISA and platform
profiles. A consumer that meets an unrecognized fault class rejects it; per
`docs/FOUNDATION.md` law 8 it must not approximate it as a no-op.
-/
structure FaultClassId where
  /-- The fault class's nominal name. -/
  name : Name
deriving DecidableEq, Repr

namespace FaultClassId

/-- A page was not present, or its permissions denied the access. -/
def pageFault : FaultClassId := ⟨⟨"pageFault"⟩⟩

/-- A general protection violation. -/
def generalProtection : FaultClassId := ⟨⟨"generalProtection"⟩⟩

/-- An alignment check violation. -/
def alignmentCheck : FaultClassId := ⟨⟨"alignmentCheck"⟩⟩

/-- A stack segment fault. -/
def stackFault : FaultClassId := ⟨⟨"stackFault"⟩⟩

/-- A device-reported access failure. -/
def deviceFault : FaultClassId := ⟨⟨"deviceFault"⟩⟩

end FaultClassId

/--
How much of an access actually happened.

Reads and writes are counted **separately**, for the reason `Committed` counts
them separately: a read-modify-write that observed its operand and faulted before
storing committed eight bytes of read and none of write, and one number cannot say
that. A single count was carried here until review pointed out that the separation
`Committed` gained stopped at the outcome and never reached the status — so the
event recorded `max`, and `committedBytes` answered eight for an access that wrote
nothing.

§1 requires a profile to state which earlier effects survive a later substep's
fault, which is why the counts are carried at all.
-/
inductive AccessStatus where
  /-- Every byte the access named took effect, for each thing its intent said it
  would do. -/
  | completed
  /-- The access stopped early without faulting, having observed `reads` bytes and
  written `writes`. -/
  | partialCommit (reads writes : Nat)
  /-- The access faulted having observed `reads` bytes and written `writes`. -/
  | faulted (fault : FaultClassId) (reads writes : Nat)
deriving DecidableEq, Repr

namespace AccessStatus

/-- The number of bytes this outcome *wrote*, given the size the access named.
The count an initialization or framing argument wants: what a read observed does
not change memory. -/
def committedWrites : AccessStatus → Nat → Nat
  | .completed, size => size
  | .partialCommit _ writes, _ => writes
  | .faulted _ _ writes, _ => writes

/-- The number of bytes this outcome *observed*, given the size the access
named. -/
def committedReads : AccessStatus → Nat → Nat
  | .completed, size => size
  | .partialCommit reads _, _ => reads
  | .faulted _ reads _, _ => reads

/-- `status.IsComplete` holds when the whole access took effect.

Nothing in `Grass/` consumes this yet; M8's consistency model is its intended
reader. Worth knowing that it was false for every load and store this model could
perform until `AccessOutcome.status`'s completeness test was made intent-relative,
which review found by asking what a completed load reports — a predicate with no
consumer is a predicate nothing was checking. -/
def IsComplete : AccessStatus → Prop
  | .completed => True
  | _ => False

instance : (status : AccessStatus) → Decidable status.IsComplete
  | .completed => .isTrue trivial
  | .partialCommit _ _ | .faulted _ _ _ => .isFalse (fun h => h)

/-- `status.IsFaulted` holds when the access raised an architectural fault. -/
def IsFaulted : AccessStatus → Prop
  | .faulted _ _ _ => True
  | _ => False

instance : (status : AccessStatus) → Decidable status.IsFaulted
  | .faulted _ _ _ => .isTrue trivial
  | .completed | .partialCommit _ _ => .isFalse (fun h => h)

/--
`status.WellFormed size` holds when neither committed count exceeds the size the
access named.

A status committing more bytes than the access covered would describe an effect
outside the access's own range, which no profile may declare. Both counts, because
a status that bounded only the larger of them would let the other exceed the range
unnoticed — which is what a single conflated count did.
-/
def WellFormed (status : AccessStatus) (size : Nat) : Prop :=
  status.committedReads size ≤ size ∧ status.committedWrites size ≤ size

instance (status : AccessStatus) (size : Nat) : Decidable (status.WellFormed size) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem committedWrites_completed (size : Nat) :
    AccessStatus.completed.committedWrites size = size := rfl

@[simp] theorem committedReads_completed (size : Nat) :
    AccessStatus.completed.committedReads size = size := rfl

@[simp] theorem wellFormed_completed (size : Nat) :
    AccessStatus.completed.WellFormed size := ⟨Nat.le_refl _, Nat.le_refl _⟩

@[simp] theorem not_isComplete_faulted (fault : FaultClassId) (reads writes : Nat) :
    ¬ (AccessStatus.faulted fault reads writes).IsComplete := fun h => h

/--
A faulting access is not a no-op. Its committed prefixes are exactly what it says,
and a proof may not assume either is zero.
-/
theorem committedWrites_faulted (fault : FaultClassId) (reads writes size : Nat) :
    (AccessStatus.faulted fault reads writes).committedWrites size = writes := rfl

/-- **A faulted read-modify-write can report a read it kept and a write it did
not make.** The outcome `Committed`'s two counts exist for, now expressible at the
status as well; it was not, and the event recorded the maximum of the two. -/
theorem committedReads_faulted (fault : FaultClassId) (reads writes size : Nat) :
    (AccessStatus.faulted fault reads writes).committedReads size = reads := rfl

end AccessStatus

/--
Whether an operation may be restarted after an interruption or fault.

`docs/MEMORY_MODEL.md` §7.4 requires restartable or partially executed
instructions to declare the state handlers observe them from and the rules for
retry. `Grass.Op.FacetName.restartability` is how a profile demands it and
`Grass.Op.OperationFacets.Closes` is the check, so this has no default.

**Declared and not enforced.** `StepPolicy.requiredFacets` can demand the facet
exist, and `AccessDescriptor.restartability` carries a value, but nothing in the
transition reads either, so `docs/MEMORY_MODEL.md` §7.4's retry rules have no
mechanism behind them here. `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 records it.
Note also that this field *does* default, to `.notRestartable`, which is the
conservative direction but is the defaulting discipline `FaultVisibility`
deliberately refuses.
-/
inductive Restartability where
  /-- The operation may be re-executed from its start with the same effect. -/
  | restartable
  /-- The operation may not be re-executed; retrying repeats committed effects. -/
  | notRestartable
  /-- A retry discipline owned by one profile. -/
  | profileSpecific (name : Name)
deriving DecidableEq, Repr

end Grass.Memory
