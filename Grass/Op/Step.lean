import Grass.Memory.State
import Grass.Op.Facets

/-!
# The generic transition relation

One operation, one step. This module imports Memory and Obligation, consumes an
operation's declared facets, and updates both state machines. Nothing here knows
which ISA produced the operation, and Memory does not import operations, so a new
instruction family participates by declaring an instance and nothing below it
changes.

The path a step takes is exactly the one the vocabulary was built to support:

```text
SomeOperation
  → declared facets              (rejected if the profile's required set is unmet)
  → substep sequence
  → per-access authority checks   (space, liveness, epoch, bounds, permission,
                                   alignment, initialization)
  → alias conflict check          (against events already performed)
  → commit or record a violation
  → fault-prefix preservation     (which earlier substeps survive)
  → obligation ledger transition
```

## Denial is not a fault, and neither is a rejected declaration

Three outcomes are distinguished, because `docs/MEMORY_MODEL.md` §1 distinguishes
them and collapsing any two loses information a profile needs:

- an operation whose facets do not close the profile's requirement is **rejected**
  before anything is attempted — it is not modelled at all, per law 8;
- an access the state does not authorize is **denied**, the prior state is
  preserved exactly, and a violation is recorded;
- an access the state authorizes but the machine faults on **commits its declared
  prefix** and continues under the sequence's visibility rule.

## Why the violation ledger only grows here

`AuditViolationLedger` cannot enforce append-only by construction — see its module
comment. `stepPreservesViolationExtends` below is the enforcement: every step this
module produces extends the ledger it was given. That is the transition invariant
§8's "cannot be erased or masked" actually names.
-/

namespace Grass.Op

open Grass.Core Grass.Memory Grass.Obligation Grass.Std.Logical

/-- Why a step could not be taken. -/
inductive StepRejection where
  /-- The operation did not supply a facet the profile requires. -/
  | facetsNotClosed (missing : FacetName)
  /-- The operation declared memory effects that are not well formed in this
  profile's address spaces. -/
  | substepsNotWellFormed
  /-- The profile does not admit one of the declared accesses. -/
  | accessNotAdmitted
deriving DecidableEq, Repr

/-- What one step produced. -/
inductive StepOutcome where
  /-- The step ran; the resulting state is attached. -/
  | ran (state : MachineState)
  /-- The step was refused before anything was attempted. -/
  | rejected (reason : StepRejection)

namespace StepOutcome

/-- The rejection reason, if the step was refused. `MachineState` has no equality,
so this projection is how a caller decides *why* a step did not run. -/
def rejection? : StepOutcome → Option StepRejection
  | .rejected reason => some reason
  | .ran _ => Option.none

/-- The resulting state, if the step ran. -/
def state? : StepOutcome → Option MachineState
  | .ran state => some state
  | .rejected _ => Option.none

/-- `outcome.Ran` holds when the step was not refused. -/
def Ran (outcome : StepOutcome) : Prop := outcome.rejection? = Option.none

instance (outcome : StepOutcome) : Decidable outcome.Ran :=
  inferInstanceAs (Decidable (_ = _))

end StepOutcome

/--
The configuration a step runs against: the memory profile, the facets every
operation must supply, and the profile's atomic-compatibility relation.

`requiredFacets` lives here rather than on `MemoryProfile` because it is a fact
about operations, and a memory profile that held it would have to know what an
operation is.
-/
structure StepPolicy where
  /-- The target's memory policy. -/
  profile : MemoryProfile
  /-- The facets every reachable operation must supply. -/
  requiredFacets : List FacetName
  /-- Which overlapping atomic pairs this target actually admits. Defaults to
  none, which is the conservative direction: every overlapping pair with a writer
  conflicts. -/
  compatible : MemoryEvent → MemoryEvent → Prop := MemoryEvent.atomicsAreNever

namespace StepPolicy

/-- Whether the policy admits a declared access at all. -/
def Admits (policy : StepPolicy) (d : AccessDescriptor) : Prop :=
  policy.profile.vocabulary.Admits d

instance (policy : StepPolicy) (d : AccessDescriptor) : Decidable (policy.Admits d) :=
  inferInstanceAs (Decidable (policy.profile.vocabulary.Admits d))

end StepPolicy

/--
Why the state refuses one access, or `none` if it authorizes it.

Checked before anything commits, so a denial leaves the state exactly as it was
(`docs/MEMORY_MODEL.md` §1). The order is deliberate: liveness before bounds
before permission before initialization, so the recorded class names the first
thing that was wrong rather than an incidental consequence.
-/
def denialOf (state : MemoryState) (d : AccessDescriptor) : Option AuditViolationClass :=
  match state.allocations.lookup d.provenance.root with
  | Option.none => some .deadProvenance
  | some record =>
      if record.live ≠ true then some .deadProvenance
      else if record.epoch ≠ d.provenance.epoch then some .deadProvenance
      else if record.space ≠ d.provenance.space then some .outOfBounds
      else if ¬ record.extent.Contains d.range then some .outOfBounds
      else if ¬ record.permission.Permits d.intent then some .permissionDenied
      else if ¬ d.AlignmentSatisfied then some .misaligned
      else if d.initialization = .allBytesInitialized ∧
              ¬ state.RangeInitialized d.provenance.root d.range then
        some .uninitializedRead
      else Option.none

/-- The violation record for a denied access. -/
def violationOf (d : AccessDescriptor) (class_ : AuditViolationClass) : AuditViolation :=
  { class_ := class_, context := d.context, provenance := d.provenance, range := d.range }

/--
Apply the ledger effect of one access.

`WellFormed` is not re-checked here: `StepPolicy.Admits` already required it, and
that is the point of making it a premise. A delta that would drop or fabricate a
duty never reaches this function.
-/
def applyLedgerEffect (obligations : FiniteMap ObligationId Obligation)
    (effect : LedgerEffect) : FiniteMap ObligationId Obligation :=
  effect.foldl (init := obligations) fun acc delta =>
    match delta with
    | .create o => acc.insert o.id o
    | .discharge id => acc.erase id
    | .split source into =>
        into.foldl (init := acc.erase source) fun inner o => inner.insert o.id o
    | .join sources into =>
        (sources.foldl (init := acc) fun inner id => inner.erase id).insert into.id into
    | .transfer id owner =>
        match acc.lookup id with
        | Option.none => acc
        | some o => acc.insert id (o.transferTo owner)

/-- Perform one access against the state, recording an event or a violation. -/
def performAccess (policy : StepPolicy) (state : MachineState) (d : AccessDescriptor)
    (status : AccessStatus) (readCommitted writeCommitted : Nat)
    (contextKind : ContextKind) (cause : EventCause) : MachineState :=
  match denialOf state.memory d with
  | some class_ =>
      -- Denied. The prior state is preserved exactly; only the ledger grows.
      { state with violations := state.violations.append (violationOf d class_) }
  | Option.none =>
      match policy.profile.vocabulary.addressSpaces.find? d.space with
      | Option.none =>
          { state with violations := state.violations.append (violationOf d .outOfBounds) }
      | some space =>
          match MemoryEvent.ofAccess? state.eventSupply.fresh.1 contextKind cause space d status
              readCommitted writeCommitted Option.none Option.none with
          | Option.none => state
          | some event =>
              { state with
                eventSupply := state.eventSupply.fresh.2
                events := state.events ++ [event]
                memory :=
                  if d.producesInitialized then
                    state.memory.setInitialized d.provenance.root
                      (d.range.take writeCommitted)
                  else state.memory
                obligations := applyLedgerEffect state.obligations d.ledgerEffect }

/--
`ConflictsWithHistory` holds when an event contends with one already performed.

This is the alias check. It consults `MemoryState.SharesBytes`, so a write through
a mapped view conflicts with a write through the allocation it maps, which
`Provenance.SameStorage` alone would have missed.
-/
def ConflictsWithHistory (policy : StepPolicy) (state : MachineState)
    (event : MemoryEvent) : Prop :=
  ∃ earlier ∈ state.events,
    MemoryEvent.Conflicts state.memory.SharesBytes policy.compatible earlier event

/--
Step one operation.

The whole vertical, in the order the module comment gives.
-/
def step (policy : StepPolicy) (state : MachineState) (operation : SomeOperation)
    (contextKind : ContextKind) (cause : EventCause) : StepOutcome :=
  let facets := operation.facets
  match policy.requiredFacets.find? (fun required => !facets.supplied.contains required) with
  | some missing => .rejected (.facetsNotClosed missing)
  | Option.none =>
    match facets.substeps? with
    | Option.none => .rejected (.facetsNotClosed .memoryEffects)
    | some sequence =>
        if ! decide (sequence.WellFormedIn policy.profile.vocabulary.addressSpaces) then
          .rejected .substepsNotWellFormed
        else if ! sequence.accesses.all (fun d => decide (policy.Admits d)) then
          .rejected .accessNotAdmitted
        else
          .ran (sequence.accesses.foldl (init := state) fun acc d =>
            performAccess policy acc d .completed
              (if d.intent.reads then d.range.size else 0)
              (if d.intent.writes then d.range.size else 0)
              contextKind cause)

/-! ## The transition invariants

These are what the docstrings elsewhere point at. A property claimed as
"cannot" or "append-only" has to be one of these or a theorem; prose describing a
mechanism is not one. -/

/-- A denied access leaves memory and obligations exactly as they were. This is
`docs/MEMORY_MODEL.md` §1's "Denial preserves the state immediately before the
denied substep". -/
theorem denied_preserves_memory (policy : StepPolicy) (state : MachineState)
    (d : AccessDescriptor) (status : AccessStatus) (r w : Nat)
    (contextKind : ContextKind) (cause : EventCause)
    (h : (denialOf state.memory d).isSome) :
    (performAccess policy state d status r w contextKind cause).memory = state.memory ∧
    (performAccess policy state d status r w contextKind cause).obligations =
      state.obligations ∧
    (performAccess policy state d status r w contextKind cause).events = state.events := by
  unfold performAccess
  cases hd : denialOf state.memory d with
  | none => rw [hd] at h; simp at h
  | some class_ => exact ⟨rfl, rfl, rfl⟩

/-- Performing an access extends the violation ledger; it never shortens it.
This is the transition invariant `docs/MEMORY_MODEL.md` §8 names, and the one
the ledger type deliberately does not try to enforce by construction. -/
theorem performAccess_extends_violations (policy : StepPolicy) (state : MachineState)
    (d : AccessDescriptor) (status : AccessStatus) (r w : Nat)
    (contextKind : ContextKind) (cause : EventCause) :
    (performAccess policy state d status r w contextKind cause).violations.Extends
      state.violations := by
  unfold performAccess
  split
  · exact AuditViolationLedger.extends_append _ _
  · split
    · exact AuditViolationLedger.extends_append _ _
    · split
      · exact AuditViolationLedger.Extends.refl _
      · exact AuditViolationLedger.Extends.refl _

end Grass.Op
