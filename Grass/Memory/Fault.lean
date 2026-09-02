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

`committed` is the count of bytes whose effect is visible afterwards. It is
carried by every non-complete outcome because §1 requires a profile to state
which earlier effects survive a later substep's fault, and a status that omitted
the count could not express that.
-/
inductive AccessStatus where
  /-- Every byte the access named took effect. -/
  | completed
  /-- The access stopped early without faulting, committing `committed` bytes. -/
  | partialCommit (committed : Nat)
  /-- The access faulted after committing `committed` bytes. -/
  | faulted (fault : FaultClassId) (committed : Nat)
deriving DecidableEq, Repr

namespace AccessStatus

/-- The number of bytes this outcome committed, given the size the access named. -/
def committedBytes : AccessStatus → Nat → Nat
  | .completed, size => size
  | .partialCommit committed, _ => committed
  | .faulted _ committed, _ => committed

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
  | .partialCommit _ | .faulted _ _ => .isFalse (fun h => h)

/-- `status.IsFaulted` holds when the access raised an architectural fault. -/
def IsFaulted : AccessStatus → Prop
  | .faulted _ _ => True
  | _ => False

instance : (status : AccessStatus) → Decidable status.IsFaulted
  | .faulted _ _ => .isTrue trivial
  | .completed | .partialCommit _ => .isFalse (fun h => h)

/--
`status.WellFormed size` holds when the committed count does not exceed the size
the access named.

A status committing more bytes than the access covered would describe an effect
outside the access's own range, which no profile may declare.
-/
def WellFormed (status : AccessStatus) (size : Nat) : Prop :=
  status.committedBytes size ≤ size

instance (status : AccessStatus) (size : Nat) : Decidable (status.WellFormed size) :=
  inferInstanceAs (Decidable (_ ≤ _))

@[simp] theorem committedBytes_completed (size : Nat) :
    AccessStatus.completed.committedBytes size = size := rfl

@[simp] theorem wellFormed_completed (size : Nat) :
    AccessStatus.completed.WellFormed size := Nat.le_refl _

@[simp] theorem not_isComplete_faulted (fault : FaultClassId) (committed : Nat) :
    ¬ (AccessStatus.faulted fault committed).IsComplete := fun h => h

/--
A faulting access is not a no-op. Its committed prefix is exactly what it says,
and a proof may not assume it is zero.
-/
theorem committedBytes_faulted (fault : FaultClassId) (committed size : Nat) :
    (AccessStatus.faulted fault committed).committedBytes size = committed := rfl

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
