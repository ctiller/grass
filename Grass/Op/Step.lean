import Grass.Memory.Apply
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
The oracle that reads committed bytes out of the memory state.

What `Oracle.zeroed` was a placeholder for. An access that reads observes what
the byte store holds, so a load after a store to the same bytes observes what the
store wrote — `Tests/Op/FakeIsa.lean`'s `a_load_observes_the_prior_store`.

Two things it does not invent.

`writeData` is a parameter, not a computation. What a store writes is the
operation's data, and `AccessDescriptor` does not carry it: the descriptor says
which bytes an access touches and what it is allowed to do to them, and putting
values on it would make every well-formedness proof about ranges also about
contents. A profile supplies the data because a profile is what knows it.

`indeterminate` is a parameter for the same reason and a stronger one. Bytes that
are not initialized have no value the model can read off the store, and
`AccessDescriptor.initialization` lets a profile permit reading them — an access
demanding `.allBytesInitialized` never reaches this, because `denialOf` refuses
it as `uninitializedRead` first. So this is reached only where a profile has
already said an indeterminate read is admissible, and the profile then owes what
such a read observes. Defaulting it to zero would be `docs/FOUNDATION.md` law 8's
permissive fallback wearing a plausible number: a program reading uninitialized
memory would observe a definite value the machine never promised, and every proof
downstream would inherit that promise.
-/
def Oracle.ofMemory
    (writeData : MachineState → AccessDescriptor → ByteSeq)
    (indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte) : Oracle where
  answer state d :=
    { observed :=
        if d.intent.reads then
          some (observedBytes state.memory d (indeterminate state d))
        else Option.none
      written :=
        if d.intent.writes then some ((writeData state d).take d.range.size)
        else Option.none
      observedPresent := by intro h; simp [h]
      observedAbsent := by intro h; simp [h]
      writtenPresent := by intro h; simp [h]
      writtenAbsent := by intro h; simp [h]
      observedFits := by
        intro bytes hb
        split at hb
        · cases hb; simp [observedBytes]
        · exact absurd hb (by simp)
      writtenFits := by
        intro bytes hb
        split at hb
        · cases hb; simp; omega
        · exact absurd hb (by simp) }

/--
An extensible source of authority evidence.

`denialOf` checks what the memory state itself knows: liveness, space, bounds,
permission, initialization. Those are fixed, because they are what an allocation
record means. Authority is open-ended. `docs/MEMORY_MODEL.md` §3 has loans, §5.1 has pins, §6
has frame lifetimes, §7.4 has lock tokens, and §7.5 has device queue ownership;
`MemoryProfile` does not enumerate them, and a fixed list here would have to.

A provider is a predicate the profile carries. `refusalOf` consults every one
after its own checks, so adding an authority kind is adding a provider — not
changing `AccessDescriptor`, `OperationFacets`, `HasOperationFacets`,
`SomeOperation`, or the shape of `step`. `Tests/Op/FakeIsa.lean` adds two, a loan
and a stack frame, with no edit under `Grass/`.

`refuses` is `Bool` rather than `Prop` for the reason `StepPolicy.compatible` is:
the transition has to run the check, and a `Prop`-valued field would make it
undecidable and the check documentation.
-/
structure AuthorityProvider where
  /-- This provider's nominal identity, for diagnostics and profile declaration. -/
  id : Name
  /-- The class recorded when it refuses.

  Open nominal, so a profile names its own. `StepPolicy.violationClassesDeclared`
  requires the profile to declare it, via `AuthorityProvider.emittedClasses`. -/
  violationClass : AuditViolationClass
  /-- Whether this provider refuses the access against the given state. -/
  refuses : MachineState → AccessDescriptor → Bool

namespace AuthorityProvider

/--
Every violation class a transition configured with these providers can record.

The transition's own fixed list, plus one class per provider.

The provider list is where this stopped being a fixed set. `violationClass` is an
open nominal field, so a profile can name a class of its own; an earlier version
of `StepPolicy.violationClassesDeclared` quantified only over
`AuditViolationClass.emittedByTransition`, which meant a provider carrying a fresh
undeclared class satisfied the proof and the transition then recorded a class the
profile's vocabulary never admitted. The closure property in
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §3.11 is that every emitted class is
declared, and it is only true if the quantified set grows with the providers.
-/
def emittedClasses (providers : List AuthorityProvider) : List AuditViolationClass :=
  AuditViolationClass.emittedByTransition ++
    providers.map AuthorityProvider.violationClass

/-- A provider's class is one of the classes its policy can emit. -/
theorem mem_emittedClasses_of_provider {providers : List AuthorityProvider}
    {provider : AuthorityProvider} (h : provider ∈ providers) :
    provider.violationClass ∈ emittedClasses providers :=
  List.mem_append_right _ (List.mem_map_of_mem h)

/-- A class the transition itself emits is one of the classes its policy can
emit, whatever the providers are. -/
theorem mem_emittedClasses_of_transition {providers : List AuthorityProvider}
    {class_ : AuditViolationClass}
    (h : class_ ∈ AuditViolationClass.emittedByTransition) :
    class_ ∈ emittedClasses providers :=
  List.mem_append_left _ h

end AuthorityProvider

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
  /-- Authority providers this profile consults, in order. Empty means the
  profile checks no authority beyond what the memory state itself knows, which is
  the right default only for a target that has none. -/
  authorities : List AuthorityProvider := []
  /-- The profile declares every violation class this relation can record.

  Without it `AdmittedVocabulary.auditViolationClasses` was a registry nothing
  consulted, while the module comment on `Grass/Memory/Profile.lean` claimed
  every registry was. A profile that has not declared `permissionDenied` cannot
  be stepped, rather than silently recording a class it never admitted.

  The set is `AuthorityProvider.emittedClasses authorities`, which depends on the
  provider list rather than being fixed. Quantifying over the fixed list alone
  left the open nominal `AuthorityProvider.violationClass` unconstrained, so a
  provider with a fresh class satisfied this proof and `refusalOf` then recorded
  a class the vocabulary never admitted. `refusalOf_class_declared` is the
  theorem that this field now actually supports. -/
  violationClassesDeclared :
    ∀ class_ ∈ AuthorityProvider.emittedClasses authorities,
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


/-- The violation record for a denied access. -/
def violationOf (d : AccessDescriptor) (class_ : AuditViolationClass) : AuditViolation :=
  { class_ := class_, context := d.context, provenance := d.provenance, range := d.range }

/--
Apply one delta to the ledger.

Factored out of the fold so that `LedgerEffectApplicable` and `applyLedgerEffect`
walk the same evolution. Only ever reached for a delta applicability has accepted.
-/
def applyDelta (obligations : FiniteMap ObligationId Obligation)
    (delta : LedgerDelta) : FiniteMap ObligationId Obligation :=
  match delta with
  | .create _ _ o => obligations.insert o.id o
  | .discharge _ _ id => obligations.erase id
  | .split _ _ source into =>
      into.foldl (init := obligations.erase source) fun inner o => inner.insert o.id o
  | .join _ _ sources into =>
      (sources.foldl (init := obligations) fun inner id => inner.erase id).insert
        into.id into
  | .transfer _ _ id owner =>
      match obligations.lookup id with
      | Option.none => obligations
      | some o => obligations.insert id (o.transferTo owner)

/--
`LedgerEffectApplicable` holds when every delta of an effect can lawfully act on
the ledger the deltas before it left.

`StepPolicy.Admits` already required `LedgerEffect.WellFormed`, which checks
*shape*. Shape is not enough and the gap was not hypothetical: with shape alone
this transition fabricated duties from identities that were never live, dropped
duties by discharging identities that were not there, and collapsed two `create`s
of one identity into one row. `docs/OBLIGATIONS.md` §2 names all three.

Liveness is a fact about the state, so it cannot be checked at admission and is
checked here.

**Each delta is checked against the ledger the previous ones left.** An earlier
version checked every delta against the *initial* map, which reintroduced at the
whole-effect level exactly the duplication `LedgerDelta.Applicable` closes at the
delta level: two `create`s of one initially-fresh identity are each individually
applicable against the initial map, and the fold then inserts one over the other
and loses a duty. Threading `applyDelta` through both makes applicability and
application walk one evolution, so checking the first tells you about the second.
-/
def LedgerEffectApplicable (obligations : FiniteMap ObligationId Obligation) :
    LedgerEffect → Prop
  | [] => True
  | delta :: rest =>
      LedgerDelta.Applicable obligations.domain
        (fun id => (obligations.lookup id).map Obligation.protocol) delta ∧
      LedgerEffectApplicable (applyDelta obligations delta) rest

instance decLedgerEffectApplicable (obligations : FiniteMap ObligationId Obligation) :
    (effect : LedgerEffect) → Decidable (LedgerEffectApplicable obligations effect)
  | [] => .isTrue trivial
  | delta :: rest =>
      have : Decidable (LedgerEffectApplicable (applyDelta obligations delta) rest) :=
        decLedgerEffectApplicable (applyDelta obligations delta) rest
      inferInstanceAs (Decidable (_ ∧ _))

/-- Apply a whole effect, one delta at a time. -/
def applyLedgerEffect (obligations : FiniteMap ObligationId Obligation)
    (effect : LedgerEffect) : FiniteMap ObligationId Obligation :=
  effect.foldl applyDelta obligations
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
        match policy.authorities.find? (fun provider => provider.refuses state d) with
        | some provider => some provider.violationClass
        | Option.none =>
            match prospective with
            | some event =>
                if ConflictsWithHistory policy state event then some .authorityUnavailable
                else Option.none
            | Option.none => Option.none

/-- Every class `denialOf` can return is one the transition declares. -/
theorem denialOf_mem_emittedByTransition {state : MemoryState} {d : AccessDescriptor}
    {class_ : AuditViolationClass} (h : denialOf state d = some class_) :
    class_ ∈ AuditViolationClass.emittedByTransition := by
  unfold denialOf at h
  repeat' split at h
  all_goals
    first
      | (injection h with h; subst h; simp [AuditViolationClass.emittedByTransition])
      | exact absurd h (by simp)

/--
Every class `refusalOf` can return is one the policy's providers and the
transition between them can emit.

The bridge between the open nominal `AuthorityProvider.violationClass` and the
declaration proof `StepPolicy` carries. Without the provider branch this was the
step that quietly widened the emitted set past what the profile had declared.
-/
theorem refusalOf_mem_emittedClasses {policy : StepPolicy} {state : MachineState}
    {d : AccessDescriptor} {prospective : Option MemoryEvent}
    {class_ : AuditViolationClass}
    (h : refusalOf policy state d prospective = some class_) :
    class_ ∈ AuthorityProvider.emittedClasses policy.authorities := by
  unfold refusalOf at h
  split at h
  · rename_i denied hd
    injection h with h
    subst h
    exact AuthorityProvider.mem_emittedClasses_of_transition
      (denialOf_mem_emittedByTransition hd)
  · split at h
    · injection h with h
      subst h
      exact AuthorityProvider.mem_emittedClasses_of_transition
        (by simp [AuditViolationClass.emittedByTransition])
    · split at h
      · rename_i provider hfind
        injection h with h
        subst h
        exact AuthorityProvider.mem_emittedClasses_of_provider
          (List.mem_of_find?_eq_some hfind)
      · repeat' split at h
        all_goals
          first
            | (injection h with h; subst h
               exact AuthorityProvider.mem_emittedClasses_of_transition
                 (by simp [AuditViolationClass.emittedByTransition]))
            | exact absurd h (by simp)

/--
**Every violation class the transition records is one the profile declared.**

The closure property `docs/MEMORY_IMPLEMENTATION_PLAN.md` §3.11 names. It holds
for authority-provider refusals as well as the transition's own, which is what
`StepPolicy.violationClassesDeclared` quantifying over
`AuthorityProvider.emittedClasses` buys.
-/
theorem refusalOf_class_declared {policy : StepPolicy} {state : MachineState}
    {d : AccessDescriptor} {prospective : Option MemoryEvent}
    {class_ : AuditViolationClass}
    (h : refusalOf policy state d prospective = some class_) :
    policy.profile.vocabulary.auditViolationClasses.Recognizes class_ :=
  policy.violationClassesDeclared class_ (refusalOf_mem_emittedClasses h)

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
                -- Through `MemoryState.commit`, which is also what
                -- `Grass/Memory/Apply.lean`'s `applyAccess` writes through, so
                -- the framing laws proved there are laws about this transition
                -- rather than about a parallel implementation. An earlier
                -- version wrote memory here directly and review found it.
                --
                -- The bytes are the ones the write actually completed, not the
                -- ones it asked for: `Committed.writtenFits` bounds them by the
                -- range, and `docs/MEMORY_MODEL.md` §4 credits initialization
                -- only to the bytes a write completes. `producesInitialized`
                -- rides along rather than gating the write, because a
                -- non-initializing write still changes the values it wrote.
                memory :=
                  state.memory.commit d (outcome.committed?.bind Committed.written)
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
    (context : ContextId) (contextKind : ContextKind) (cause : EventCause) :
    FaultPlan sequence → MachineState
  | .none => runAccesses policy state sequence.accesses contextKind cause
  | .before index fault committed =>
      match sequence.visibleEffects? index.val with
      | Option.none => state
      | some survivors =>
          -- The fault is recorded before the branch on what kind of substep
          -- faulted, so no branch can discard it. An earlier version took the
          -- fault as an argument and dropped it wherever the faulting substep was
          -- not an access -- which is exactly the compute substep a divide faults
          -- on, so the one case the `compute` constructor exists for was the one
          -- that lost its fault.
          let survived := runAccesses policy state survivors contextKind cause
          let faulted :=
            { survived with
              faults := survived.faults ++
                [{ fault := fault, context := context, cause := cause
                   substep := index.val }] }
          match sequence.substeps[index.val]? with
          | some (.access d) =>
              performAccess policy faulted d
                (.faulted fault ((policy.oracle.answer faulted d).truncate committed))
                contextKind cause
          | _ => faulted

/--
Step one operation.

The whole vertical, in the order the module comment gives. `faultAt` says whether
the machine faulted and where, as a function of the sequence so that the index it
names is in range by construction.

`context` is the executing context. It is an operation-level argument because a
faulting substep need not be an access, so there is not always a descriptor to
read one from — `docs/MEMORY_MODEL.md` §7.1 wants context identity *and* kind on
every event, and this supplies the identity for a fault that touches no bytes.
-/
def step (policy : StepPolicy) (state : MachineState) (operation : SomeOperation)
    (context : ContextId) (contextKind : ContextKind) (cause : EventCause)
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
          | .none => .ran (runStep policy state sequence context contextKind cause .none)
          | .before index fault committed =>
              match sequence.visibleEffects? index.val with
              | Option.none => .rejected .visibilityRuleUnknown
              | some _ =>
                  .ran (runStep policy state sequence context contextKind cause
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
    (sequence : SubstepSequence) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) (plan : FaultPlan sequence) :
    (runStep policy state sequence context contextKind cause plan).violations.Extends
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

/-! ## The memory framing laws apply to this transition

`Grass/Memory/Apply.lean` proves framing over `MemoryState.commit`. Because
`performAccess` writes through `commit` and nothing else, those laws are laws
about `step`. These theorems are the statement of that, and they exist because
review found the earlier arrangement — two write paths, framing proved about one
of them, and prose claiming it covered both. -/

/--
**Performing an access frames every cell it did not declare.**

`Committed.writtenFits` supplies the bound `Grass.Memory.WrittenFits` wants, so
the transition satisfies the hypothesis by construction rather than by a caller
promising it.
-/
theorem performAccess_frames_untouched (policy : StepPolicy) (state : MachineState)
    (d : AccessDescriptor) (outcome : AccessOutcome d) (contextKind : ContextKind)
    (cause : EventCause) {id : AllocId} {offset : Nat}
    (h : ¬ (d.provenance.root = id ∧ d.range.Covers offset)) :
    (performAccess policy state d outcome contextKind cause).memory.cellAt? id offset =
      state.memory.cellAt? id offset := by
  unfold performAccess
  repeat' split
  all_goals
    first
      | rfl
      | exact Grass.Memory.cellAt?_commit_of_untouched state.memory d
          (fun bytes hb => by
            cases hc : outcome.committed? with
            | none => rw [hc] at hb; exact absurd hb (by simp)
            | some c =>
              rw [hc] at hb
              simp only [Option.bind_some] at hb
              exact c.writtenFits bytes hb) h

/--
**A whole run of accesses frames every cell none of them declared.**

The form a straight-line argument over `step` uses. `runAccesses` stops at the
first refusal, and this holds whether it ran to the end or stopped early, because
every branch either performs an access or returns the state.
-/
theorem runAccesses_frames_untouched (policy : StepPolicy) {id : AllocId} {offset : Nat} :
    ∀ (accesses : List AccessDescriptor) (state : MachineState) (contextKind : ContextKind)
      (cause : EventCause),
      (∀ d ∈ accesses, ¬ (d.provenance.root = id ∧ d.range.Covers offset)) →
      (runAccesses policy state accesses contextKind cause).memory.cellAt? id offset =
        state.memory.cellAt? id offset
  | [], _, _, _, _ => rfl
  | d :: rest, state, contextKind, cause, hall => by
    have hhead := performAccess_frames_untouched policy state d
      (AccessOutcome.completed (policy.oracle.answer state d)) contextKind cause
      (hall d List.mem_cons_self)
    show (if (performAccess policy state d (.completed (policy.oracle.answer state d))
              contextKind cause).violations.recordCount = state.violations.recordCount then
            runAccesses policy (performAccess policy state d
              (.completed (policy.oracle.answer state d)) contextKind cause) rest
              contextKind cause
          else performAccess policy state d (.completed (policy.oracle.answer state d))
              contextKind cause).memory.cellAt? id offset = _
    split
    · rw [runAccesses_frames_untouched policy rest _ contextKind cause
        (fun x hx => hall x (List.mem_cons_of_mem _ hx))]
      exact hhead
    · exact hhead

/-- Performing an access does not touch the fault record: a fault is raised by a
substep, and `performAccess` runs one access. -/
theorem performAccess_preserves_faults (policy : StepPolicy) (state : MachineState)
    (d : AccessDescriptor) (outcome : AccessOutcome d) (contextKind : ContextKind)
    (cause : EventCause) :
    (performAccess policy state d outcome contextKind cause).faults = state.faults := by
  unfold performAccess
  repeat' split
  all_goals rfl

/--
**A recorded fault is never discarded.**

Every branch of a faulting run appends the fault before deciding what kind of
substep failed, so the fault the machine reported is present in the resulting
state whether or not that substep touched memory. An earlier version dropped it
on the non-access branch, which is exactly the compute substep a divide faults
on — the one case `Substep.compute` exists for was the one that lost its fault.
-/
theorem runStep_records_the_fault (policy : StepPolicy) (state : MachineState)
    (sequence : SubstepSequence) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) (index : Fin sequence.substeps.length) (fault : FaultClassId)
    (committed : Nat) (survivors : List AccessDescriptor)
    (hvisible : sequence.visibleEffects? index.val = some survivors) :
    ∃ record ∈ (runStep policy state sequence context contextKind cause
      (.before index fault committed)).faults, record.fault = fault := by
  show ∃ record ∈ (match sequence.visibleEffects? index.val with
    | Option.none => state
    | some survivors =>
        let survived := runAccesses policy state survivors contextKind cause
        let faulted :=
          { survived with
            faults := survived.faults ++
              [({ fault := fault, context := context, cause := cause
                  substep := index.val } : RaisedFault)] }
        match sequence.substeps[index.val]? with
        | some (.access d) =>
            performAccess policy faulted d
              (.faulted fault ((policy.oracle.answer faulted d).truncate committed))
              contextKind cause
        | _ => faulted).faults, record.fault = fault
  rw [hvisible]
  simp only []
  split
  · rw [performAccess_preserves_faults]
    exact ⟨{ fault := fault, context := context, cause := cause, substep := index.val },
      by simp, rfl⟩
  · exact ⟨{ fault := fault, context := context, cause := cause, substep := index.val },
      by simp, rfl⟩

/--
**Every step extends the violation ledger.**

This is the theorem the module comment points at, and the transition invariant
`docs/MEMORY_MODEL.md` §8 actually names. A rejection produces no state at all; a
run produces `runStep`, which extends.
-/
theorem step_extends_violations (policy : StepPolicy) (state : MachineState)
    (operation : SomeOperation) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence) (final : MachineState)
    (h : step policy state operation context contextKind cause faultAt = .ran final) :
    final.violations.Extends state.violations := by
  unfold step at h
  repeat' split at h
  all_goals
    first
      | exact StepOutcome.noConfusion h
      | (injection h with h; subst h; exact runStep_extends_violations _ _ _ _ _ _ _)

/--
**Every event a step records is well formed.**

True by construction: `MachineState.events` holds `ValidMemoryEvent`, whose
well-formedness is a field, and `MemoryEvent.ofOutcome` is the only producer.
Stated anyway, because it is the property M8's consistency model depends on and a
reader should be able to find it named rather than infer it from a type.
-/
theorem step_events_wellFormed (policy : StepPolicy) (state : MachineState)
    (operation : SomeOperation) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence) (final : MachineState)
    (_ : step policy state operation context contextKind cause faultAt = .ran final) :
    ∀ valid ∈ final.events, valid.event.WellFormed :=
  final.events_wellFormed

end Grass.Op
