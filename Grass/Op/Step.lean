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
How the machine answered an access.

The transition does not invent this. Which bytes a load observed is a fact about
memory, a device, or a previous substep, and an `AccessDescriptor` is a static
declaration that cannot carry it — an earlier bridge passed `none` for both values
and minted a trace of events that violated the project's own well-formedness
predicate.

An `Oracle` supplies the answer. A profile backs it with the byte store, a device
model, or recorded results; this module only requires that whatever it returns is
a `Committed` for the descriptor in question, which ties the byte counts to the
intent by construction.
-/
structure Oracle where
  /-- What the machine committed for this access, given the state it ran against. -/
  answer : MachineState → (d : AccessDescriptor) → Committed d

/--
The oracle that commits the whole named range with zero-valued bytes.

Enough to exercise the transition without a byte store, and honest about what it
is: it reports the counts the intent implies and supplies zero bytes of content.
M2's store replaces it. It is *not* a default — `StepPolicy` requires an oracle,
so a profile chooses this one deliberately.
-/
def Oracle.zeroed : Oracle where
  answer _ d :=
    { observed := if d.intent.reads then some (List.replicate d.range.size 0) else Option.none
      written := if d.intent.writes then some (List.replicate d.range.size 0) else Option.none
      observedPresent := by intro h; simp [h]
      observedAbsent := by intro h; simp [h]
      writtenPresent := by intro h; simp [h]
      writtenAbsent := by intro h; simp [h]
      observedFits := by
        intro bytes hb
        split at hb
        · cases hb; simp
        · exact absurd hb (by simp)
      writtenFits := by
        intro bytes hb
        split at hb
        · cases hb; simp
        · exact absurd hb (by simp) }

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
  /-- How the machine answers an access. Required, not defaulted: what a load
  observed is a fact about the target, and a transition that invented it would be
  inventing the trace M8 reads. -/
  oracle : Oracle
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
code. The cross-context case is the one this can decide today; the general
happens-before that would let two contexts be *proved* ordered is M8's. Until
then, denying every cross-context conflict is the conservative direction — it can
refuse a program a synchronizing profile would allow, never admit a racy one.
-/
def ConflictsWithHistory (policy : StepPolicy) (state : MachineState)
    (event : MemoryEvent) : Prop :=
  ∃ earlier ∈ state.events,
    earlier.event.context.id ≠ event.context.id ∧
    MemoryEvent.Conflicts state.memory.SharesBytes
      (fun a b => policy.compatible a b = true) earlier.event event

instance (policy : StepPolicy) (state : MachineState) (event : MemoryEvent) :
    Decidable (ConflictsWithHistory policy state event) :=
  inferInstanceAs (Decidable (∃ earlier ∈ state.events,
    earlier.event.context.id ≠ event.context.id ∧
    MemoryEvent.Conflicts state.memory.SharesBytes
      (fun a b => policy.compatible a b = true) earlier.event event))

/--
Why this access is refused, or `none` if nothing refuses it.

Every reason an access can be denied, in one place and one order, so that the
recorded class names the first thing that was wrong. `docs/MEMORY_MODEL.md` §1
requires the check to happen before anything commits; `performAccess` calls this
first and commits only on `none`.

`prospective` is the event the access *would* record, needed for the alias check.
-/
def refusalOf (policy : StepPolicy) (state : MachineState) (d : AccessDescriptor)
    (prospective : Option MemoryEvent) : Option AuditViolationClass :=
  match denialOf state.memory d with
  | some class_ => some class_
  | Option.none =>
      if ¬ LedgerEffectApplicable state.obligations d.ledgerEffect then
        some .obligationNotAuthorized
      else
        match prospective with
        | some event =>
            if ConflictsWithHistory policy state event then some .authorityUnavailable
            else Option.none
        | Option.none => Option.none

/--
Perform one access, recording a certified event or a violation.

The shape is the one `docs/MEMORY_MODEL.md` §1 demands: every authority check runs
against the pre-access state, gathered by `refusalOf`, and the access commits
only on `none`.
A refusal leaves memory, obligations, events, and the event supply exactly as they
were and appends to the violation ledger — see `refused_preserves_everything_but_the_ledger`.
-/
def performAccess (policy : StepPolicy) (state : MachineState) (d : AccessDescriptor)
    (outcome : AccessOutcome d) (contextKind : ContextKind) (cause : EventCause) :
    MachineState :=
  match policy.profile.vocabulary.addressSpaces.find? d.space with
  | Option.none =>
      { state with
        violations := state.violations.append (violationOf d .wrongAddressSpace) }
  | some space =>
      match MemoryEvent.ofOutcome state.eventSupply.fresh.1 contextKind cause space d
          outcome with
      | Option.none =>
          -- The outcome committed nothing, so there is no event. A denial carries
          -- its own violation; anything else touched no bytes.
          match outcome.violation? with
          | some violation => { state with violations := state.violations.append violation }
          | Option.none => state
      | some valid =>
          match refusalOf policy state d (some valid.event) with
          | some class_ =>
              { state with violations := state.violations.append (violationOf d class_) }
          | Option.none =>
              { state with
                eventSupply := state.eventSupply.fresh.2
                events := state.events ++ [valid]
                memory :=
                  match outcome.committed? with
                  | some c =>
                      if d.producesInitialized then
                        state.memory.setInitialized d.provenance.root
                          (d.range.take c.writeCount)
                      else state.memory
                  | Option.none => state.memory
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
def runAccesses (policy : StepPolicy) (state : MachineState)
    (accesses : List AccessDescriptor) (contextKind : ContextKind) (cause : EventCause) :
    MachineState :=
  match accesses with
  | [] => state
  | d :: rest =>
      let next :=
        performAccess policy state d (.completed (policy.oracle.answer state d))
          contextKind cause
      if next.violations.recordCount = state.violations.recordCount then
        runAccesses policy next rest contextKind cause
      else
        next

/--
Where an operation faulted, if it did.

`before index` names the substep that did not complete, and `index` is a `Fin`
over the sequence, so an out-of-range fault is **unrepresentable**. It used to be
a bare `Nat`: `visibleEffects?` then took the whole list, the substep lookup
missed, and the fallback committed every access to completion while `step`
returned `.ran` — a reported fault silently becoming a successful operation.

The stepper takes this rather than inventing it. Which substep of a `rep movsb`
faults is a fact about the machine at that moment, and a transition relation that
predicted it would be modelling something else.
-/
inductive FaultPlan (sequence : SubstepSequence) where
  /-- Every substep completed. -/
  | none
  /-- The substep at `index` did not complete, raising `fault` after committing
  `committed` bytes. -/
  | before (index : Fin sequence.substeps.length) (fault : FaultClassId) (committed : Nat)

/--
The state a running step produces.

Split out from `step` so that every branch which runs funnels through one
function. `step` decides whether to run; this decides what running does. The
separation is what makes `step_extends_violations` a short proof rather than a
case analysis over the rejection paths, and it means a new rejection reason
cannot silently acquire an unproved state transition.
-/
def runStep (policy : StepPolicy) (state : MachineState) (sequence : SubstepSequence)
    (contextKind : ContextKind) (cause : EventCause) : FaultPlan sequence → MachineState
  | .none => runAccesses policy state sequence.accesses contextKind cause
  | .before index fault committed =>
      match sequence.visibleEffects? index.val with
      | Option.none => state
      | some survivors =>
          match sequence.substeps[index.val]? with
          | some (.access d) =>
              let after := runAccesses policy state survivors contextKind cause
              performAccess policy after d
                (.faulted fault ((policy.oracle.answer after d).truncate committed))
                contextKind cause
          | _ => runAccesses policy state survivors contextKind cause

/--
Step one operation.

The whole vertical, in the order the module comment gives. `faultAt` says whether
the machine faulted and where, as a function of the sequence so that the index it
names is in range by construction.
-/
def step (policy : StepPolicy) (state : MachineState) (operation : SomeOperation)
    (contextKind : ContextKind) (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence :=
      fun _ => .none) : StepOutcome :=
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
          match faultAt sequence with
          | .none => .ran (runStep policy state sequence contextKind cause .none)
          | .before index fault committed =>
              match sequence.visibleEffects? index.val with
              | Option.none => .rejected .visibilityRuleUnknown
              | some _ =>
                  .ran (runStep policy state sequence contextKind cause
                    (.before index fault committed))

/-! ## The transition invariants

These are the properties the docstrings elsewhere point at. Under the rule in
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §3.10, a comment saying "ensures",
"prevents", "cannot", "only", or "preserves" must name one of these or a type;
otherwise it is an intended invariant or an open obligation and says so. -/

/--
**A refused access changes nothing but the violation ledger.**

Every refusal path, not one. `refusalOf` gathers them — the state's own denial,
an inapplicable ledger effect, an alias conflict — so a new refusal reason cannot
acquire an unproved transition. `docs/MEMORY_MODEL.md` §1: "Denial preserves the
state immediately before the denied substep."
-/
theorem refused_preserves_everything_but_the_ledger (policy : StepPolicy)
    (state : MachineState) (d : AccessDescriptor) (outcome : AccessOutcome d)
    (contextKind : ContextKind) (cause : EventCause) (space : AddressSpace)
    (hspace : policy.profile.vocabulary.addressSpaces.find? d.space = some space)
    (valid : ValidMemoryEvent)
    (hevent : MemoryEvent.ofOutcome state.eventSupply.fresh.1 contextKind cause space d
      outcome = some valid)
    (class_ : AuditViolationClass)
    (hrefused : refusalOf policy state d (some valid.event) = some class_) :
    (performAccess policy state d outcome contextKind cause).memory = state.memory ∧
    (performAccess policy state d outcome contextKind cause).obligations =
      state.obligations ∧
    (performAccess policy state d outcome contextKind cause).events = state.events ∧
    (performAccess policy state d outcome contextKind cause).eventSupply =
      state.eventSupply := by
  unfold performAccess
  rw [hspace]
  simp only []
  rw [hevent]
  simp only []
  rw [hrefused]
  exact ⟨rfl, rfl, rfl, rfl⟩

/--
**The ledger changes exactly when the access commits.**

`applyLedgerEffect` runs on the committing branch and nowhere else, so a refused
access — for any reason, including an inapplicable ledger effect — leaves the
obligations untouched. This is the "ledger mutation occurs iff the delta is
applicable" half that a fold could not give.
-/
theorem obligations_unchanged_unless_committed (policy : StepPolicy)
    (state : MachineState) (d : AccessDescriptor) (outcome : AccessOutcome d)
    (contextKind : ContextKind) (cause : EventCause)
    (hrefused : ∀ space valid,
      policy.profile.vocabulary.addressSpaces.find? d.space = some space →
      MemoryEvent.ofOutcome state.eventSupply.fresh.1 contextKind cause space d outcome
        = some valid →
      (refusalOf policy state d (some valid.event)).isSome) :
    (performAccess policy state d outcome contextKind cause).obligations =
      state.obligations := by
  unfold performAccess
  split
  · rfl
  · rename_i space hspace
    split
    · split <;> rfl
    · rename_i valid hevent
      have := hrefused space valid hspace hevent
      cases hr : refusalOf policy state d (some valid.event) with
      | none => rw [hr] at this; simp at this
      | some class_ => rfl

/--
**A refusal prevents every later effect of the operation.**

`runAccesses` returns the refused state itself, so no access after the refused one
is attempted. This is the theorem behind "denial stops the ordinary instruction
path": a platform operation that genuinely continues past a failure needs its own
declared sequencing policy and its own theorem, and folding the rest anyway is
not that.
-/
theorem runAccesses_stops_at_refusal (policy : StepPolicy) (state : MachineState)
    (d : AccessDescriptor) (rest : List AccessDescriptor) (contextKind : ContextKind)
    (cause : EventCause)
    (hrefused :
      (performAccess policy state d (.completed (policy.oracle.answer state d))
        contextKind cause).violations.recordCount ≠ state.violations.recordCount) :
    runAccesses policy state (d :: rest) contextKind cause =
      performAccess policy state d (.completed (policy.oracle.answer state d))
        contextKind cause := by
  rw [runAccesses]
  simp [hrefused]

/--
**A refused ledger mutation is recorded, not silent.**

The companion to `obligations_unchanged_unless_committed`: an inapplicable delta
does not merely fail to apply, it appends to the violation ledger. Together they
are `docs/OBLIGATIONS.md` §2's requirement that a forbidden change be refused
*and* visible — a fold that silently no-opped satisfied neither.
-/
theorem ledger_refusal_is_recorded (policy : StepPolicy) (state : MachineState)
    (d : AccessDescriptor) (outcome : AccessOutcome d) (contextKind : ContextKind)
    (cause : EventCause) (space : AddressSpace) (valid : ValidMemoryEvent)
    (hspace : policy.profile.vocabulary.addressSpaces.find? d.space = some space)
    (hevent : MemoryEvent.ofOutcome state.eventSupply.fresh.1 contextKind cause space d
      outcome = some valid)
    (hallowed : denialOf state.memory d = Option.none)
    (hledger : ¬ LedgerEffectApplicable state.obligations d.ledgerEffect) :
    (performAccess policy state d outcome contextKind cause).violations.recordCount =
      state.violations.recordCount + 1 := by
  unfold performAccess
  rw [hspace]
  simp only []
  rw [hevent]
  simp only []
  have : refusalOf policy state d (some valid.event) = some .obligationNotAuthorized := by
    unfold refusalOf
    rw [hallowed]
    simp [hledger]
  rw [this]
  simp

/-- Performing an access extends the violation ledger; it never shortens it.
This is the per-access form of the invariant `docs/MEMORY_MODEL.md` §8 names, and
the one the ledger type deliberately does not try to enforce by construction. -/
theorem performAccess_extends_violations (policy : StepPolicy) (state : MachineState)
    (d : AccessDescriptor) (outcome : AccessOutcome d)
    (contextKind : ContextKind) (cause : EventCause) :
    (performAccess policy state d outcome contextKind cause).violations.Extends
      state.violations := by
  unfold performAccess
  split
  · exact AuditViolationLedger.extends_append _ _
  · split
    · split
      · exact AuditViolationLedger.extends_append _ _
      · exact AuditViolationLedger.Extends.refl _
    · split
      · exact AuditViolationLedger.extends_append _ _
      · exact AuditViolationLedger.Extends.refl _

/-- Running a list of accesses extends the violation ledger, including when it
stops early at a refusal. Built from the per-access form above. -/
theorem runAccesses_extends_violations (policy : StepPolicy) (state : MachineState)
    (accesses : List AccessDescriptor) (contextKind : ContextKind) (cause : EventCause) :
    (runAccesses policy state accesses contextKind cause).violations.Extends
      state.violations := by
  induction accesses generalizing state with
  | nil => exact AuditViolationLedger.Extends.refl _
  | cons d rest ih =>
    have hp := performAccess_extends_violations policy state d
      (.completed (policy.oracle.answer state d)) contextKind cause
    rw [runAccesses]
    split
    · exact AuditViolationLedger.Extends.trans hp (ih _)
    · exact hp

/-- Running a step extends the violation ledger, whichever shape the run takes:
the whole sequence, a surviving prefix, or a prefix followed by the faulting
access itself. -/
theorem runStep_extends_violations (policy : StepPolicy) (state : MachineState)
    (sequence : SubstepSequence) (contextKind : ContextKind) (cause : EventCause)
    (plan : FaultPlan sequence) :
    (runStep policy state sequence contextKind cause plan).violations.Extends
      state.violations := by
  unfold runStep
  split
  · exact runAccesses_extends_violations _ _ _ _ _
  · split
    · exact AuditViolationLedger.Extends.refl _
    · split
      · exact AuditViolationLedger.Extends.trans
          (runAccesses_extends_violations _ _ _ _ _)
          (performAccess_extends_violations _ _ _ _ _ _)
      · exact runAccesses_extends_violations _ _ _ _ _

/--
**Every step extends the violation ledger.**

This is the theorem the module comment points at, and the transition invariant
`docs/MEMORY_MODEL.md` §8 actually names. A rejection produces no state at all; a
run produces `runStep`, which extends.
-/
theorem step_extends_violations (policy : StepPolicy) (state : MachineState)
    (operation : SomeOperation) (contextKind : ContextKind) (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence) (final : MachineState)
    (h : step policy state operation contextKind cause faultAt = .ran final) :
    final.violations.Extends state.violations := by
  unfold step at h
  repeat' split at h
  all_goals
    first
      | exact StepOutcome.noConfusion h
      | (injection h with h; subst h; exact runStep_extends_violations _ _ _ _ _ _)

/--
**Every event a step records is well formed.**

True by construction: `MachineState.events` holds `ValidMemoryEvent`, whose
well-formedness is a field, and `MemoryEvent.ofOutcome` is the only producer.
Stated anyway, because it is the property M8's consistency model depends on and a
reader should be able to find it named rather than infer it from a type.
-/
theorem step_events_wellFormed (policy : StepPolicy) (state : MachineState)
    (operation : SomeOperation) (contextKind : ContextKind) (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence) (final : MachineState)
    (_ : step policy state operation contextKind cause faultAt = .ran final) :
    ∀ valid ∈ final.events, valid.event.WellFormed :=
  final.events_wellFormed

end Grass.Op
