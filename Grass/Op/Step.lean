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
comment. `step_extends_violations` below is the enforcement: every step this
module produces extends the ledger it was given, whether it ran to completion,
denied an access, or honoured a fault. That is the transition invariant §8's
"cannot be erased or masked" actually names.
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
  /-- The operation faulted under a visibility rule this relation cannot read.
  The rule belongs to a profile, and guessing which effects survive would be
  worse than refusing. -/
  | visibilityRuleUnknown
  /-- The machine reported a fault at a substep the operation does not have.
  Refused rather than ignored: treating an out-of-range index as "no fault"
  would turn a reported fault into a completed operation. -/
  | faultPointOutOfRange
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
  /-- The profile declares every violation class this relation can record.

  Without it `AdmittedVocabulary.auditViolationClasses` was a registry nothing
  consulted, while the module comment on `Grass/Memory/Profile.lean` claimed
  every registry was. A profile that has not declared `permissionDenied` cannot
  be stepped, rather than silently recording a class it never admitted. -/
  violationClassesDeclared :
    ∀ class_ ∈ AuditViolationClass.emittedByTransition,
      profile.vocabulary.auditViolationClasses.Recognizes class_
  /-- The profile's vocabulary is coherent.

  A field rather than a check inside `step`, so a policy with an incoherent
  vocabulary cannot be constructed at all. A vocabulary that declared one
  address-space identity twice with different representations would make which
  version an access was checked against depend on list order. -/
  vocabularyWellFormed : profile.vocabulary.WellFormed
  /-- Which overlapping atomic pairs this target actually admits. Defaults to
  none, which is the conservative direction: every overlapping pair with a writer
  conflicts. `Bool`-valued so the stepper can actually run the check; a
  `Prop`-valued field would have made the conflict test undecidable and the check
  would have quietly become documentation. -/
  compatible : MemoryEvent → MemoryEvent → Bool := fun _ _ => false

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

/-- The violation record for a denied access. -/
def violationOf (d : AccessDescriptor) (class_ : AuditViolationClass) : AuditViolation :=
  { class_ := class_, context := d.context, provenance := d.provenance, range := d.range }

/--
`LedgerEffectApplicable` holds when every delta of an effect can lawfully act on
the obligations actually outstanding.

`StepPolicy.Admits` already required `LedgerEffect.WellFormed`, which checks
*shape*. Shape is not enough and the gap was not hypothetical: with shape alone
this transition fabricated duties from identities that were never live, dropped
duties by discharging identities that were not there, and collapsed two `create`s
of one identity into one row. `docs/OBLIGATIONS.md` §2 names all three.

Liveness is a fact about the state, so it cannot be checked at admission and is
checked here.
-/
def LedgerEffectApplicable (obligations : FiniteMap ObligationId Obligation)
    (effect : LedgerEffect) : Prop :=
  ∀ delta ∈ effect,
    LedgerDelta.Applicable obligations.domain
      (fun id => (obligations.lookup id).map Obligation.protocol) delta

instance (obligations : FiniteMap ObligationId Obligation) (effect : LedgerEffect) :
    Decidable (LedgerEffectApplicable obligations effect) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/--
Apply the ledger effect of one access.

Only ever called on an effect `LedgerEffectApplicable` has accepted, so every
consumed identity is live and every produced one is fresh.
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

/--
`ConflictsWithHistory` holds when an event contends with one already performed.

This is the alias check, and `performAccess` calls it: an access whose event would
conflict with one already in the trace is denied and recorded, exactly like an
access the state refuses on any other ground.

It consults `MemoryState.SharesBytes`, so a write through a mapped view conflicts
with a write through the allocation it maps — which `Provenance.SameStorage` alone
would have missed, because those are distinct allocations by construction.

**Distinct contexts only.** `docs/MEMORY_MODEL.md` §7.3 defines a race over
"conflicting events from distinct concurrent contexts... unordered by
happens-before". Two writes by one context to the same bytes are not a race:
program order sequences them, and denying them would refuse ordinary sequential
code. The cross-context case is the one this can decide today; the same-context
ordering is sequenced-before, and the general happens-before that would let two
contexts be *proved* ordered is M8's. Until then, denying every cross-context
conflict is the conservative direction — it can refuse a program a synchronizing
profile would allow, never admit a racy one.
-/
def ConflictsWithHistory (policy : StepPolicy) (state : MachineState)
    (event : MemoryEvent) : Prop :=
  ∃ earlier ∈ state.events,
    earlier.context.id ≠ event.context.id ∧
    MemoryEvent.Conflicts state.memory.SharesBytes
      (fun a b => policy.compatible a b = true) earlier event

instance (policy : StepPolicy) (state : MachineState) (event : MemoryEvent) :
    Decidable (ConflictsWithHistory policy state event) :=
  inferInstanceAs (Decidable (∃ earlier ∈ state.events,
    earlier.context.id ≠ event.context.id ∧
    MemoryEvent.Conflicts state.memory.SharesBytes
      (fun a b => policy.compatible a b = true) earlier event))

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
              if ¬ LedgerEffectApplicable state.obligations d.ledgerEffect then
                -- The declared ledger effect is not authorized against the
                -- obligations actually outstanding. Nothing commits.
                { state with
                  violations :=
                    state.violations.append (violationOf d .obligationNotAuthorized) }
              else if ConflictsWithHistory policy state event then
                -- An alias conflict is an authority failure, not a fault: the
                -- access is refused and nothing commits.
                { state with
                  violations := state.violations.append (violationOf d .authorityUnavailable) }
              else
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
Where an operation faulted, if it did.

The stepper takes this rather than inventing it: which substep of a `rep movsb`
faults is a fact about the machine at that moment, and the transition relation's
job is to say what the state looks like afterwards, not to predict it.
-/
structure FaultPoint where
  /-- The index of the substep that did not complete. -/
  index : Nat
  /-- The fault it raised. -/
  fault : FaultClassId
  /-- How many bytes that substep committed before faulting, if it was an access.
  A faulting access is not a no-op, and `docs/MEMORY_MODEL.md` §1 forbids assuming
  it is. -/
  committed : Nat
deriving DecidableEq, Repr

/--
Perform the accesses that survive, in order, stopping at the first denial.

**Stopping is the point.** An earlier version folded over every access
unconditionally, so an operation whose first substep was denied for dead
provenance still committed its second. That is a continue-after-denial policy no
operation declared and no document states, invented silently in the one place
`docs/FOUNDATION.md` law 8 targets. `SubstepSequence.onFault` is the declared
answer to what survives a failure, and it is about faults; a denial is not a
fault, and the conservative reading is that the operation does not proceed.

`visibleEffects?` decides which accesses are attempted at all, and returning
`none` for a profile-owned visibility rule is why `step` can reject: the generic
relation does not know what an x86 split-page store exposes.
-/
def committedCounts (d : AccessDescriptor) : Nat × Nat :=
  (if d.intent.reads then d.range.size else 0,
   if d.intent.writes then d.range.size else 0)

def runAccesses (policy : StepPolicy) (state : MachineState)
    (accesses : List AccessDescriptor) (contextKind : ContextKind) (cause : EventCause) :
    MachineState :=
  match accesses with
  | [] => state
  | d :: rest =>
      let next :=
        performAccess policy state d .completed
          (committedCounts d).1 (committedCounts d).2 contextKind cause
      if next.violations.recordCount = state.violations.recordCount then
        runAccesses policy next rest contextKind cause
      else
        next

/--
The state a running step produces.

Split out from `step` so that every branch which runs funnels through one
function. `step` decides whether to run; this decides what running does. The
separation is what makes `step_extends_violations` a short proof rather than a
case analysis over the rejection paths, and it means a new rejection reason
cannot silently acquire an unproved state transition.
-/
def runStep (policy : StepPolicy) (state : MachineState) (sequence : SubstepSequence)
    (contextKind : ContextKind) (cause : EventCause) : Option FaultPoint → MachineState
  | Option.none => runAccesses policy state sequence.accesses contextKind cause
  | some point =>
      match sequence.visibleEffects? point.index with
      | Option.none => state
      | some survivors =>
          match sequence.substeps[point.index]? with
          | some (.access d) =>
              performAccess policy (runAccesses policy state survivors contextKind cause) d
                (.faulted point.fault point.committed)
                (if d.intent.reads then min point.committed d.range.size else 0)
                (if d.intent.writes then min point.committed d.range.size else 0)
                contextKind cause
          | _ => runAccesses policy state survivors contextKind cause

/--
Step one operation.

The whole vertical, in the order the module comment gives. `faultAt` says whether
the machine faulted and where; `none` means every substep completed.
-/
def step (policy : StepPolicy) (state : MachineState) (operation : SomeOperation)
    (contextKind : ContextKind) (cause : EventCause)
    (faultAt : Option FaultPoint := Option.none) : StepOutcome :=
  match policy.requiredFacets.find?
      (fun required => !operation.facets.supplied.contains required) with
  | some missing =>
      -- `OperationFacets.Closes` is the predicate this decides; `find?` is how the
      -- failing facet is named, so a rejection says *which* one is missing rather
      -- than only that closure failed.
      .rejected (.facetsNotClosed missing)
  | Option.none =>
    match operation.facets.substeps? with
    | Option.none => .rejected (.facetsNotClosed .memoryEffects)
    | some sequence =>
        if ! decide (sequence.WellFormedIn policy.profile.vocabulary.addressSpaces) then
          .rejected .substepsNotWellFormed
        else if ! sequence.accesses.all (fun d => decide (policy.Admits d)) then
          .rejected .accessNotAdmitted
        else
          match faultAt with
          | Option.none => .ran (runStep policy state sequence contextKind cause Option.none)
          | some point =>
              if point.index ≥ sequence.substeps.length then
                .rejected .faultPointOutOfRange
              else
                match sequence.visibleEffects? point.index with
                | Option.none => .rejected .visibilityRuleUnknown
                | some _ => .ran (runStep policy state sequence contextKind cause (some point))

/-! ## The transition invariants

These are what the docstrings elsewhere point at. A property claimed as
"cannot" or "append-only" has to be one of these or a theorem; prose describing a
mechanism is not one. -/

/-- A denied access leaves memory and obligations exactly as they were. This is
`docs/MEMORY_MODEL.md` §1's "Denial preserves the state immediately before the
denied substep". -/
theorem denied_preserves_everything_but_the_ledger (policy : StepPolicy)
    (state : MachineState) (d : AccessDescriptor) (status : AccessStatus) (r w : Nat)
    (contextKind : ContextKind) (cause : EventCause)
    (h : (denialOf state.memory d).isSome) :
    (performAccess policy state d status r w contextKind cause).memory = state.memory ∧
    (performAccess policy state d status r w contextKind cause).obligations =
      state.obligations ∧
    (performAccess policy state d status r w contextKind cause).events = state.events ∧
    (performAccess policy state d status r w contextKind cause).eventSupply =
      state.eventSupply := by
  unfold performAccess
  cases hd : denialOf state.memory d with
  | none => rw [hd] at h; simp at h
  | some class_ => exact ⟨rfl, rfl, rfl, rfl⟩

/--
The other two denial paths preserve everything but the ledger too.

`denialOf` is not the only way an access is refused: an inapplicable ledger effect
and an alias conflict both deny after it passes. An earlier version proved
preservation only for the `denialOf` branch, so the two branches added later were
uncovered — and named three of the state's five fields, which is not "the state is
untouched" however true it happened to be.
-/
theorem ledger_denial_preserves_everything_but_the_ledger (policy : StepPolicy)
    (state : MachineState) (d : AccessDescriptor) (status : AccessStatus) (r w : Nat)
    (contextKind : ContextKind) (cause : EventCause)
    (hallowed : denialOf state.memory d = Option.none)
    (h : ¬ LedgerEffectApplicable state.obligations d.ledgerEffect) :
    (performAccess policy state d status r w contextKind cause).memory = state.memory ∧
    (performAccess policy state d status r w contextKind cause).obligations =
      state.obligations ∧
    (performAccess policy state d status r w contextKind cause).events = state.events ∧
    (performAccess policy state d status r w contextKind cause).eventSupply =
      state.eventSupply := by
  unfold performAccess
  rw [hallowed]
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl, rfl, rfl⟩
        · rename_i hn
          exact (hn h).elim

/-- Performing an access extends the violation ledger; it never shortens it.
This is the per-access form of the invariant `docs/MEMORY_MODEL.md` §8 names, and
the one the ledger type deliberately does not try to enforce by construction. -/
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
      · split
        · exact AuditViolationLedger.extends_append _ _
        · split
          · exact AuditViolationLedger.extends_append _ _
          · exact AuditViolationLedger.Extends.refl _

/-- Running a list of accesses extends the violation ledger, including when it
stops early at a denial. Built from the per-access form above. -/
theorem runAccesses_extends_violations (policy : StepPolicy) (state : MachineState)
    (accesses : List AccessDescriptor) (contextKind : ContextKind) (cause : EventCause) :
    (runAccesses policy state accesses contextKind cause).violations.Extends
      state.violations := by
  induction accesses generalizing state with
  | nil => exact AuditViolationLedger.Extends.refl _
  | cons d rest ih =>
    have hp := performAccess_extends_violations policy state d .completed
      (committedCounts d).1 (committedCounts d).2 contextKind cause
    rw [runAccesses]
    split
    · exact AuditViolationLedger.Extends.trans hp (ih _)
    · exact hp

/-- Running a step extends the violation ledger, whichever shape the run takes:
the whole sequence, a surviving prefix, or a prefix followed by the faulting
access itself. -/
theorem runStep_extends_violations (policy : StepPolicy) (state : MachineState)
    (sequence : SubstepSequence) (contextKind : ContextKind) (cause : EventCause)
    (faultAt : Option FaultPoint) :
    (runStep policy state sequence contextKind cause faultAt).violations.Extends
      state.violations := by
  unfold runStep
  split
  · exact runAccesses_extends_violations _ _ _ _ _
  · split
    · exact AuditViolationLedger.Extends.refl _
    · split
      · exact AuditViolationLedger.Extends.trans
          (runAccesses_extends_violations _ _ _ _ _)
          (performAccess_extends_violations _ _ _ _ _ _ _ _)
      · exact runAccesses_extends_violations _ _ _ _ _

/--
**Every step extends the violation ledger.**

This is the theorem the module comment points at, and the transition invariant
`docs/MEMORY_MODEL.md` §8 actually names. A rejection produces no state at all; a
run produces `runStep`, which extends. An earlier module comment named a theorem
`stepPreservesViolationExtends` that did not exist, and only the per-access and
per-list forms were proved, leaving the fault path's composition uncovered.
-/
theorem step_extends_violations (policy : StepPolicy) (state : MachineState)
    (operation : SomeOperation) (contextKind : ContextKind) (cause : EventCause)
    (faultAt : Option FaultPoint) (final : MachineState)
    (h : step policy state operation contextKind cause faultAt = .ran final) :
    final.violations.Extends state.violations := by
  unfold step at h
  repeat' split at h
  all_goals
    first
      | exact StepOutcome.noConfusion h
      | (injection h with h; subst h; exact runStep_extends_violations _ _ _ _ _ _)

end Grass.Op
