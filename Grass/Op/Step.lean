import Grass.Memory.Loan
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
  | accessNotAdmitted (reason : AdmittedVocabulary.AdmissibilityFailure)
  /-- The operation faulted under a visibility rule this relation cannot read.
  The rule belongs to a profile, and guessing which effects survive would be
  worse than refusing. -/
  | visibilityRuleUnknown
  /-- The machine reported a fault class the faulting substep does not declare.

  `Substep.faults` is what an access or a compute step says it may raise, and
  `AdmittedVocabulary.Admits` already requires an access's `admittedFaults` to be
  recognized by the vocabulary. Nothing consulted either, so a `FaultPlan` could
  name a class no registry admitted and the transition would record it — into
  `RaisedFault` and into a `ValidMemoryEvent`'s status, since
  `MemoryEvent.WellFormed` constrains counts and lengths but not fault identity.
  That is `AuthorityProvider.violationClass`'s hole in a second place. Review
  found it. -/
  | faultClassNotDeclared (fault : FaultClassId)
  /-- The machine reported a fault at a substep whose access carries an obligation
  ledger effect, and the corpus does not say what becomes of that effect.

  `docs/OBLIGATIONS.md` §1 makes cancellation and fault behaviour part of an
  obligation's form and §2 requires a transition to *state* how it transforms the
  ledger. The generic relation applied the whole effect on the faulting path, so a
  `reserve` that faulted having written zero bytes still created its release duty
  and a `release` that faulted having written nothing still discharged one — the
  second is a leak. Refusing is `docs/FOUNDATION.md` law 8's answer to a rule
  nobody wrote: the profile owes a fault rule before such an operation can fault.
  See `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.3. -/
  | faultWithUndeclaredLedgerEffect
  /-- The machine reported a fault at a substep whose access carries an *authority*
  effect, and the corpus does not say what becomes of that effect either.

  The exact defect above, in the field that arrived a milestone later. `performAccess`
  applies `AccessDescriptor.authorityEffect` in full on the committing branch however
  little the access committed, so a `priorEffectsVisible` sequence whose faulting
  substep declared a lend ran it after writing zero bytes: review drove a store that
  wrote nothing to lend the buffer's head to the device engine, a faulting return to
  consume its identity, and a faulting transfer to move a grant. The gate beside this
  one was written for `ledgerEffect` and was not extended when `authorityEffect`
  landed.

  A separate constructor rather than a rename, because which effect was undeclared is
  the useful half of the report, and collapsing two distinguishable failures into one
  is a defect this layer has already closed once in `AdmissibilityFailure`. -/
  | faultWithUndeclaredAuthorityEffect
  /-- An execution context is stepped under a kind other than the one the state
  records for it.

  `docs/MEMORY_MODEL.md` §7.1 requires an event to carry identity *and* kind. The
  identity came from the descriptor and the kind from an argument, with nothing
  relating them, so one `ContextId` could be a thread in one step and a device
  engine in the next. `contextMismatch` closed the identity half and review found
  the kind half still open a round later. `MachineState.contexts` is the single
  source of truth now. -/
  | contextKindMismatch (context : ContextId) (declared recorded : ContextKind)
  /-- An access declares an executing context other than the one running the step.

  `MemoryEvent.ofOutcome` takes the event's context *identity* from
  `AccessDescriptor.context` and its *kind* from `step`'s argument, and nothing
  compared them. `ConflictsWithHistory` discriminates on that identity, so
  `docs/MEMORY_MODEL.md` §7.3's race rule — conflicting events from *distinct*
  contexts — was defeated by a one-field declaration: a device write naming the
  program thread aliased the thread's bytes and committed. The minted event also
  carried an incoherent pair, thread identity with engine kind, while §7.1 requires
  identity *and* kind. Two sources of truth for one fact, which is the defect this
  layer removed from `AllocationRecord`; review found it surviving here. -/
  | contextMismatch (declared executing : ContextId)
  /-- A compute substep declares a fault class the profile's vocabulary does not
  recognize.

  `AdmittedVocabulary.Admits` closes this for an access, because it quantifies over
  `admittedFaults`. A compute substep has no descriptor, so `sequence.accesses`
  never contains it and `Admits` never sees it — the only thing checked about one
  was that its fault list is non-empty. `faultClassNotDeclared` then validated a
  plan against a list that was itself unvalidated. Review found it, and noted that
  `.compute` is the constructor the `div` case exists for, so it is the one most
  likely to carry a profile-invented name. -/
  | computeFaultNotRecognized (fault : FaultClassId)
  /-- A fault plan claims a commit count the access could not have produced.

  `Committed.truncate` clamps by `List.take`, so an over-large count cannot
  over-claim bytes and memory stays sound. It was accepted silently, which is what
  `faultPointOutOfRange` existed to prevent for the index: a machine report the
  model knows is impossible should be refused, not approximated.

  The bound is **intent-relative**. A write-only access cannot have read anything
  — `Committed.observedAbsent` forces `readCount = 0` — so a plan claiming a read
  on a store is exactly such an impossible report, and the first version of this
  check bounded both counts by the range and let it through to be quietly rewritten
  to zero. Review found that asymmetry: an impossible count on a compute substep
  was refused while an impossible count on an access was approximated. -/
  | faultCommitOutOfRange
  /-- A substep may raise a fault class the operation's `faults` facet does not
  declare.

  `OperationFacets.faults` is what an operation says it may raise, and it was
  consumed by nothing: `OperationFacets.supplied` reads only `isSome`, so an
  operation declaring `faults := some []` closed the facet and then page-faulted
  through a substep that admitted one. The substep-level list was checked
  (`faultClassNotDeclared`); the operation-level declaration above it was not
  cross-checked against anything, which made it a fact the model carried and
  nothing consulted — the shape this layer has removed from `AllocationRecord` and
  `AccessIntent` already.

  Checked statically, on every step rather than only on a faulting one. An
  operation whose two facets contradict each other is refused before it runs,
  because `docs/FOUNDATION.md` law 8 says the answer to two declarations that
  disagree is not to pick one. Together with `faultClassNotDeclared` this gives
  what a caller reading the facet is entitled to assume: a raised class is one the
  operation declared. -/
  | operationFaultsIncomplete (fault : FaultClassId)
  /-- The operation declares a fault class the profile's vocabulary does not
  recognize.

  `AdmittedVocabulary.Admits` closes this for an access's `admittedFaults` and
  `computeFaultNotRecognized` closes it for a compute substep. The operation-level
  list was the third place a fault class could be named, and the only one no
  registry saw. `Grass/Memory/Profile.lean` requires every registry to be
  *listed*, which is weaker than every registry being consulted and was quoted here
  as the stronger claim; nothing states the stronger one, and the operation-level
  fault list was the case where it was false. -/
  | operationFaultNotRecognized (fault : FaultClassId)
  /-- The sequence's fault-visibility rule names something the profile never
  registered.

  `FaultVisibility.transactional` names the target theorem `docs/INSTRUCTIONS.md`
  §4 requires and `FaultVisibility.profileSpecific` names a rule the profile owns,
  and no registry held either. A sequence got all-or-nothing fault semantics by
  declaring a string. `SubstepSequence.visibleEffects?` already refused to guess
  what a profile rule says, but only on a faulting path, so a sequence carrying a
  name nobody had registered and not faulting ran and minted its events.

  `RequiresJustification` marks which constructors make a claim; this is the check
  that the claim was made *to* someone. It is still not the proof: a registered
  name says the profile owns the claim, not that it discharged it, and §10's
  package is where discharge lives. -/
  | onFaultRuleNotRegistered (rule : Name)
  /-- An access substep requests an ordering the operation's `ordering` facet does
  not declare.

  `OperationFacets.ordering` was the second facet consumed by nothing —
  `OperationFacets.supplied` reads only `isSome` — and `AdmitsOrder`/`AdmitsScope`
  check the *descriptor's* ordering, never the operation's. So
  `docs/INSTRUCTIONS.md` §1's "atomicity and memory ordering" declaration was a
  value nothing compared to anything, and a profile could declare an operation
  sequentially consistent over relaxed accesses, or relaxed over atomic ones. Six of
  this fixture's own operations did the latter.

  Equality, not containment, because `Grass/Memory/Ordering.lean` deliberately
  defines no strength order between modes — the relation that matters is the one a
  `ConsistencyProfile` induces over a whole event graph, which is M8's, and a
  weaker-than order defined here would be a second, unproved one. So the only
  relation this layer can state is that the two declarations agree, and law 8's
  answer to two that do not is to refuse rather than pick. `OperationFacets.ordering` is
  single-valued, so an operation whose substeps genuinely differ in ordering has no
  way to declare that and is refused here. `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2
  records it as an open obligation on the facet rather than on this check. -/
  | operationOrderingDisagrees (declared requested : OrderingDemand)
  /-- The operation declares an ordering mode or scope the profile never registered.

  `AdmitsOrder` and `AdmitsScope` check an *access descriptor's* ordering, and
  checking the operation's only through its accesses is vacuous for a sequence with
  none: a `.compute`-only operation declaring `MemoryOrder.profileSpecific` with any
  name at all stepped. Review found it, along with the fact that omitting the facet
  skips the disagreement check entirely — which is `Closes`'s question and is why
  `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 records that no policy in the tree lists
  `.ordering` as required. -/
  | operationOrderingNotRegistered (name : Name)
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
  /--
  What the machine committed for this access, or `none` if it cannot complete it.

  `CompleteCommitted` rather than `Committed`, so an answer that does not fill the
  access is not expressible as a completion. `Option`, so an oracle that cannot
  fill one has somewhere to say so — the alternative would be padding the answer,
  and inventing bytes the machine did not supply is worse than refusing.
  `runAccesses` records `machineAnswerIncomplete` and stops.
  -/
  answer : MachineState → (d : AccessDescriptor) → Option (CompleteCommitted d)

/--
The oracle that commits the whole named range with zero-valued bytes.

Enough to exercise the transition without a byte store, and honest about what it
is: it reports the counts the intent implies and supplies zero bytes of content.
M2's store replaces it. It is *not* a default — `StepPolicy` requires an oracle,
so a profile chooses this one deliberately.
-/
def Oracle.zeroed : Oracle where
  answer _ d := some
    { committed :=
        { observed :=
            if d.intent.reads then some (List.replicate d.range.size 0) else Option.none
          written :=
            if d.intent.writes then some (List.replicate d.range.size 0) else Option.none
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
      readsFull := by intro h; simp [Committed.readCount, h]
      writesFull := by intro h; simp [Committed.writeCount, h] }

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
`AccessDescriptor.initialization` lets a profile permit reading them, so the
profile that admitted such a read owes what it observes. Defaulting it to zero
would be `docs/FOUNDATION.md` law 8's permissive fallback wearing a plausible
number: a program reading uninitialized memory would observe a definite value the
machine never promised, and every proof downstream would inherit that promise.

**Note what is not true here.** `runAccesses` builds `oracle.answer state d`
before calling `performAccess`, so the oracle is consulted whether or not the
access is refused. An earlier version of this comment said `denialOf` refuses an
`.allBytesInitialized` access first; that is true of `Grass/Memory/Apply.lean`'s
`applyAccess`, which does match on `denialOf` before reading, and false here.
Review found it. What holds instead is that a refusal discards the answer:
`refused_preserves_everything_but_the_ledger` says a refused access leaves memory,
obligations, events, and the supply as they were and appends only a violation
record, which carries no bytes.
-/
def Oracle.ofMemory
    (writeData : MachineState → AccessDescriptor → ByteSeq)
    (indeterminate : MachineState → (d : AccessDescriptor) → Nat → Byte) : Oracle where
  answer state d :=
    if hfits : ¬ d.intent.writes ∨ d.range.size ≤ (writeData state d).length then
      some
        { committed :=
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
          readsFull := by
            intro h
            simp [Committed.readCount, h, observedBytes]
          writesFull := by
            intro h
            rcases hfits with hno | hlen
            · exact absurd h (by simp [hno])
            · simp [Committed.writeCount, h]
              omega }
    else
      -- Short write data is not padded and not reinterpreted. The profile said
      -- this access writes `range.size` bytes and the machine supplied fewer, so
      -- the machine description does not match the access; `runAccesses` records
      -- `machineAnswerIncomplete`.
      Option.none

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
  /-- Whether this provider refuses the access against the memory state.

  **The memory state, not the machine state.** A provider used to see the whole
  `MachineState` — events, faults, the violation ledger, the obligation table — and
  review's point was that nothing constrained what it did with any of it: a provider
  keyed on `state.events.length` was well formed, and refusal that depends on
  execution history is the ambient authority `docs/FOUNDATION.md` law 6 forbids.
  Narrowing the argument makes that unrepresentable rather than merely unwise, which
  is this layer's preferred order. All three providers in `Tests/Op/FakeIsa.lean`
  read `state.memory` and nothing else, so nothing was lost.

  What this does *not* fix is the rest of review's finding: a provider may still
  refuse arbitrarily as a function of the memory state — refuse everything, or key on
  an unrelated allocation — and `StepPolicy` still proves things about a provider's
  class and nothing about its behaviour. Monotonicity and locality-in-the-range are
  open, and `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records them. -/
  refuses : MemoryState → AccessDescriptor → Bool

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
  /-- Compatibility is a property of *atomic* pairs.

  `docs/MEMORY_MODEL.md` §7.3's sentence is "they are not both **compatible atomic
  accesses** under one profile", and the atomicity half was enforced nowhere:
  `MemoryEvent.Conflicts` never reads `ordering.atomicity`, and this field had no
  conditions at all. So a profile could declare two plain non-atomic stores
  compatible, which is not a weakening of §7.3 but a step outside it. Review set
  `compatible := fun _ _ => true` on the fixture's own profile and watched the
  cross-context pair that `aliased_cross_context_store_is_denied` denies commit with
  an empty ledger — the loan rule's defect, one field over: a policy field that can
  only *remove* a refusal, where `AuthorityProvider.refuses` can only add one.

  A proof field rather than a check, for the reason `vocabularyWellFormed` is one: a
  policy that cannot discharge it cannot be constructed. The default discharges it
  trivially, because nothing is compatible. -/
  compatibleIsAtomic : ∀ a b, compatible a b = true →
    a.ordering.atomicity = .atomic ∧ b.ordering.atomicity = .atomic := by
      intro _ _ h; exact absurd h (by simp)
  /-- And compatibility is symmetric.

  `MemoryEvent.Conflicts.symm` takes symmetry as a hypothesis and nothing discharged
  it, so whether two events conflicted depended on which one the trace saw first.
  Review built `compatible := fun a _ => decide (a.context.id = thread₀)` and got two
  events and an empty ledger stepping thread-then-engine, one event and a violation
  stepping the same two accesses engine-then-thread. A conflict is a symmetric fact
  about a pair; this field could make it not one. -/
  compatibleSymm : ∀ a b, compatible a b = true → compatible b a = true := by
      intro _ _ h; exact absurd h (by simp)

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
def LedgerEffectApplicable (obligations : FiniteMap ObligationId Obligation)
    (contexts : List ContextId) (actor : ContextId) : LedgerEffect → Prop
  | [] => True
  | delta :: rest =>
      LedgerDelta.Applicable obligations.domain
        (fun id => (obligations.lookup id).map Obligation.protocol)
        (fun id => (obligations.lookup id).map Obligation.owner)
        (fun id => (obligations.lookup id).map Obligation.kind) contexts actor delta ∧
      LedgerEffectApplicable (applyDelta obligations delta) contexts actor rest

instance decLedgerEffectApplicable (obligations : FiniteMap ObligationId Obligation)
    (contexts : List ContextId) (actor : ContextId) :
    (effect : LedgerEffect) →
      Decidable (LedgerEffectApplicable obligations contexts actor effect)
  | [] => .isTrue trivial
  | delta :: rest =>
      have : Decidable
          (LedgerEffectApplicable (applyDelta obligations delta) contexts actor rest) :=
        decLedgerEffectApplicable (applyDelta obligations delta) contexts actor rest
      inferInstanceAs (Decidable (_ ∧ _))

/--
Apply one delta, or refuse.

**One function, not a predicate and an applier.** `LedgerDelta.Applicable` says a
delta may act and `applyDelta` makes it act, and nothing tied the two together: a
clause added to one and forgotten in the other is a silent divergence, and this
branch found `Applicable` missing a clause twice — the output `kind`, then the
transfer destination — with `applyDelta` unaffected both times. Neither miss was
caught by the shape; both were caught by a reviewer.

`MemoryState.applyAuthorityDelta?` is the shape that cannot diverge from itself. The
ledger cannot be brought all the way to it without rewriting every fixture that
states `LedgerEffectApplicable`, so it is brought as far as two theorems:
`ledgerEffectApplicable_iff_isSome` says the predicate is exactly the applier
succeeding, and `applyLedgerEffect?_eq_some_of_applicable` says that on the path the
transition takes, the applier is the fold the transition installs. Tied by proof
rather than by shape, which is second best and is stated as such.
-/
def applyLedgerDelta? (obligations : FiniteMap ObligationId Obligation)
    (contexts : List ContextId) (actor : ContextId) (delta : LedgerDelta) :
    Option (FiniteMap ObligationId Obligation) :=
  if LedgerDelta.Applicable obligations.domain
      (fun id => (obligations.lookup id).map Obligation.protocol)
      (fun id => (obligations.lookup id).map Obligation.owner)
      (fun id => (obligations.lookup id).map Obligation.kind) contexts actor delta then
    some (applyDelta obligations delta)
  else Option.none

/-- Apply a whole effect, one delta at a time, refusing if any delta is refused. -/
def applyLedgerEffect? (obligations : FiniteMap ObligationId Obligation)
    (contexts : List ContextId) (actor : ContextId) :
    LedgerEffect → Option (FiniteMap ObligationId Obligation)
  | [] => some obligations
  | delta :: rest =>
      (applyLedgerDelta? obligations contexts actor delta).bind
        (applyLedgerEffect? · contexts actor rest)

/--
**The predicate and the applier are the same rule.**

`refusalOf` decides with `LedgerEffectApplicable` and `performAccess` installs
`applyLedgerEffect?`'s result, so without this they would be two descriptions of one
rule and a clause could be added to either alone. There is no longer a third
description: the unconditional fold the transition used to install is deleted, and
`applyLedgerDelta?` gates `applyDelta` behind the very predicate `refusalOf` asks
about.
-/
theorem ledgerEffectApplicable_iff_isSome (obligations : FiniteMap ObligationId Obligation)
    (contexts : List ContextId) (actor : ContextId) :
    ∀ (effect : LedgerEffect),
      LedgerEffectApplicable obligations contexts actor effect ↔
        (applyLedgerEffect? obligations contexts actor effect).isSome := by
  intro effect
  induction effect generalizing obligations with
  | nil => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | cons delta rest ih =>
    constructor
    · rintro ⟨happly, hrest⟩
      show (Option.bind _ _).isSome = true
      unfold applyLedgerDelta?
      rw [if_pos happly, Option.bind_some]
      exact (ih _).mp hrest
    · intro h
      have h' : (Option.bind (applyLedgerDelta? obligations contexts actor delta)
        (applyLedgerEffect? · contexts actor rest)).isSome = true := h
      by_cases happly : LedgerDelta.Applicable obligations.domain
          (fun id => (obligations.lookup id).map Obligation.protocol)
          (fun id => (obligations.lookup id).map Obligation.owner)
          (fun id => (obligations.lookup id).map Obligation.kind) contexts actor delta
      · refine ⟨happly, (ih _).mpr ?_⟩
        unfold applyLedgerDelta? at h'
        rw [if_pos happly, Option.bind_some] at h'
        exact h'
      · unfold applyLedgerDelta? at h'
        rw [if_neg happly, Option.bind_none] at h'
        exact absurd h' (by simp)

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
**A non-atomic overlapping pair conflicts under every policy.**

The theorem this area was missing, and the direct analogue of
`refusalOf_refuses_the_unauthorized`: it quantifies over `policy`, so no
compatibility relation a profile writes can make a race disappear.

`docs/MEMORY_MODEL.md` §7.3 exempts "compatible **atomic** accesses", and
`StepPolicy.compatibleIsAtomic` is what makes the adjective load-bearing — without it
`MemoryEvent.Conflicts` read `compatible` and nothing read `ordering.atomicity`, so a
profile could declare two plain stores compatible and step them past each other.
Review did exactly that on the fixture's own profile.
-/
theorem conflicts_of_not_atomic {policy : StepPolicy}
    {sharesBytes : AllocId → AllocId → Prop} {a b : MemoryEvent}
    (hatouch : a.kind.touchesMemory = true) (hbtouch : b.kind.touchesMemory = true)
    (hspace : a.provenance.space = b.provenance.space)
    (hshares : sharesBytes a.provenance.root b.provenance.root)
    (hoverlap : a.committedRange.Overlaps b.committedRange)
    (hwrites : a.kind.writes = true ∨ b.kind.writes = true)
    (hatomic : a.ordering.atomicity ≠ .atomic) :
    MemoryEvent.Conflicts sharesBytes (fun x y => policy.compatible x y = true) a b := by
  refine ⟨hatouch, hbtouch, hspace, hshares, hoverlap, hwrites, ?_⟩
  intro hcompatible
  exact hatomic (policy.compatibleIsAtomic a b hcompatible).1

/--
**Conflict is symmetric under any policy.**

`MemoryEvent.Conflicts.symm` takes symmetry of the compatibility relation as a
hypothesis and nothing discharged it, so whether two events conflicted could depend on
which one the trace saw first — review built a `compatible` keyed on the first
argument's context and got two events and an empty ledger one way, one event and a
violation the other. `StepPolicy.compatibleSymm` is what supplies it, and this is its
consumer.

The `sharesBytes` half is a hypothesis in the general form and discharged in the
specialised one below. It was owed for a round: `MemoryState.SharesBytes` had no
symmetry theorem, and when one was attempted the definition turned out not to admit
it — the closure quantified its intermediate over the *allocation table*, so a
one-hop path needed its far end allocated and the reversed path needed the near end
allocated. `MemoryState.aliasIdentities` is the repair and `sharesBytes_symm` is the
theorem.
-/
theorem conflicts_symm {policy : StepPolicy} {sharesBytes : AllocId → AllocId → Prop}
    {a b : MemoryEvent} (shareSymm : ∀ x y, sharesBytes x y → sharesBytes y x)
    (h : MemoryEvent.Conflicts sharesBytes (fun x y => policy.compatible x y = true) a b) :
    MemoryEvent.Conflicts sharesBytes (fun x y => policy.compatible x y = true) b a :=
  h.symm shareSymm (fun x y hxy => policy.compatibleSymm x y hxy)

/-- **And conflict over a real memory state is symmetric outright**, with nothing left
to supply: `MemoryState.sharesBytes_symm` discharges the sharing half and
`StepPolicy.compatibleSymm` the compatibility half. This is the form
`ConflictsWithHistory` would use, and the reason the two fields exist. -/
theorem conflicts_symm_of_state {policy : StepPolicy} {state : MemoryState}
    {a b : MemoryEvent}
    (h : MemoryEvent.Conflicts state.SharesBytes
      (fun x y => policy.compatible x y = true) a b) :
    MemoryEvent.Conflicts state.SharesBytes
      (fun x y => policy.compatible x y = true) b a :=
  conflicts_symm (fun _ _ hxy => MemoryState.sharesBytes_symm hxy) h

/-- The same at the trace level: an earlier event from another context that a
non-atomic access overlaps is a conflict, whatever the policy says. -/
theorem conflictsWithHistory_of_not_atomic {policy : StepPolicy} {state : MachineState}
    {event : MemoryEvent} {earlier : ValidMemoryEvent} (hmem : earlier ∈ state.events)
    (hcontext : earlier.event.context.id ≠ event.context.id)
    (hatouch : earlier.event.kind.touchesMemory = true)
    (hbtouch : event.kind.touchesMemory = true)
    (hspace : earlier.event.provenance.space = event.provenance.space)
    (hshares : state.memory.SharesBytes earlier.event.provenance.root
      event.provenance.root)
    (hoverlap : earlier.event.committedRange.Overlaps event.committedRange)
    (hwrites : earlier.event.kind.writes = true ∨ event.kind.writes = true)
    (hatomic : earlier.event.ordering.atomicity ≠ .atomic) :
    ConflictsWithHistory policy state event :=
  ⟨earlier, hmem, hcontext,
    conflicts_of_not_atomic hatouch hbtouch hspace hshares hoverlap hwrites hatomic⟩

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
      if ¬ LedgerEffectApplicable state.obligations state.contexts.domain d.context
          d.ledgerEffect then
        some .obligationNotAuthorized
      else if (state.memory.applyAuthorityEffect? d.context d.authorityEffect).isNone then
        some .authorityEffectRefused
      else if ¬ (state.memory.authorityOf d.context d.provenance d.range).PermitsIntent
                d.intent then
        -- §3's authority states, asked of *this* context: `frozen` while another
        -- holds the bytes, `sharedImmutable` while they are read-shared.
        --
        -- Both halves of the loan rule are here, and the second is not enough on its
        -- own. Two grants that did not conflict when issued are made to conflict by
        -- an alias declared afterwards, and in that state each holder is `Granted` by
        -- its own grant -- so the holder clause below passes for both, and the
        -- previous commit's claim that it subsumed the provider was wrong. A probe
        -- stepped exactly that: `aliasedAfterIssue` with no providers listed, and the
        -- thread's write committed over bytes the engine also held. `authorityOf`
        -- asks the question that sees the other holder.
        some .authorityUnavailable
      else if state.memory.AnyGrantOver d.provenance d.range ∧
              ¬ state.memory.Granted d.context d.provenance d.range d.intent then
        -- §3's loan rule, asked by the transition rather than by a provider a
        -- profile may or may not have listed. It used to live only in
        -- `AuthorityProvider.loan`, and `StepPolicy.authorities` defaults to `[]` --
        -- so a profile that declared no providers got no authority enforcement at
        -- all, and review stepped `lendSlot` to mint a grant through `step` and then
        -- walked over it with an ordinary store, no violation recorded. Every law in
        -- `Grass/Memory/Loan.lean` was conditioned on a policy field a profile author
        -- gets wrong by writing nothing, which is the ambient-authority shape
        -- `docs/FOUNDATION.md` law 6 forbids read from the other side.
        --
        -- Providers remain, for authority the *profile* adds -- a frame rule, a
        -- device rule -- and they may only add refusals. They cannot remove this one.
        some .authorityUnavailable
      else
        match policy.authorities.find? (fun provider => provider.refuses state.memory d) with
        | some provider => some provider.violationClass
        | Option.none =>
            match prospective with
            | some event =>
                if ConflictsWithHistory policy state event then some .conflictingAccess
                else Option.none
            | Option.none => Option.none

/--
**An access to bytes another context holds is refused, whatever providers the policy
lists.**

The law the loan rule was missing. It used to live in `AuthorityProvider.loan`, and
`StepPolicy.authorities` defaults to `[]`, so every theorem about the grant map was
conditioned on a policy field a profile author gets wrong by writing nothing — review
stepped an operation that minted a grant and then walked over it with an ordinary
store, no violation recorded, under a policy that differed from the fixture's in that
one field. This quantifies over `policy`, which is the whole point: no provider list
can remove the refusal, and a provider may only add its own.

The hypotheses are the clauses ahead of it in the chain, which is what makes the
statement about *this* rule rather than about whichever rule fires first.
-/
theorem refusalOf_refuses_the_unauthorized {policy : StepPolicy} {state : MachineState}
    {d : AccessDescriptor} {prospective : Option MemoryEvent}
    (hclean : denialOf state.memory d = Option.none)
    (hledger : LedgerEffectApplicable state.obligations state.contexts.domain d.context
      d.ledgerEffect)
    (hauth : (state.memory.applyAuthorityEffect? d.context d.authorityEffect).isSome)
    (hstate : (state.memory.authorityOf d.context d.provenance d.range).PermitsIntent
      d.intent)
    (hheld : state.memory.AnyGrantOver d.provenance d.range)
    (hnot : ¬ state.memory.Granted d.context d.provenance d.range d.intent) :
    refusalOf policy state d prospective = some .authorityUnavailable := by
  unfold refusalOf
  rw [hclean, if_neg (by simpa using hledger),
    if_neg (by simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using hauth),
    if_neg (by simpa using hstate), if_pos ⟨hheld, hnot⟩]

/-- And it does not fire where nothing is held, which is what stops it refusing every
access under a policy with no providers. -/
theorem refusalOf_allows_the_unheld {policy : StepPolicy} {state : MachineState}
    {d : AccessDescriptor} {prospective : Option MemoryEvent}
    (hclean : denialOf state.memory d = Option.none)
    (hledger : LedgerEffectApplicable state.obligations state.contexts.domain d.context
      d.ledgerEffect)
    (hauth : (state.memory.applyAuthorityEffect? d.context d.authorityEffect).isSome)
    (hstate : (state.memory.authorityOf d.context d.provenance d.range).PermitsIntent
      d.intent)
    (hunheld : ¬ state.memory.AnyGrantOver d.provenance d.range) :
    refusalOf policy state d prospective =
      match policy.authorities.find? (fun provider => provider.refuses state.memory d) with
      | some provider => some provider.violationClass
      | Option.none =>
          match prospective with
          | some event =>
              if ConflictsWithHistory policy state event then
                some AuditViolationClass.conflictingAccess
              else Option.none
          | Option.none => Option.none := by
  unfold refusalOf
  rw [hclean, if_neg (by simpa using hledger),
    if_neg (by simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using hauth),
    if_neg (by simpa using hstate), if_neg (fun h => hunheld h.1)]

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
      · injection h with h
        subst h
        exact AuthorityProvider.mem_emittedClasses_of_transition
          (by simp [AuditViolationClass.emittedByTransition])
      · split at h
        · injection h with h
          subst h
          exact AuthorityProvider.mem_emittedClasses_of_transition
            (by simp [AuditViolationClass.emittedByTransition])
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
**Nothing refusing the access means the declared ledger changes apply.**

The ledger's half of the same argument. `performAccess` has a branch for
`applyLedgerEffect?` returning `none` on the committing path, and this rules it out:
`refusalOf` decided with `LedgerEffectApplicable`, and `ledgerEffectApplicable_iff_isSome`
says that is exactly this function succeeding.
-/
theorem ledger_effect_applies_when_nothing_refuses {policy : StepPolicy}
    {state : MachineState} {d : AccessDescriptor} {prospective : Option MemoryEvent}
    (h : refusalOf policy state d prospective = Option.none) :
    (applyLedgerEffect? state.obligations state.contexts.domain d.context
      d.ledgerEffect).isSome := by
  unfold refusalOf at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · next happly =>
      exact (ledgerEffectApplicable_iff_isSome _ _ _ _).mp (by simpa using happly)

/--
**Nothing refusing the access means the declared authority changes apply.**

`performAccess` has a branch for the applier returning `none` on the committing
path, which this rules out: `refusalOf`'s authority clause runs the same function
against the same map, so the branch is unreachable. It records a violation rather
than falling back to the unchanged map, because a fallback there would commit an
access whose declared lend silently did not happen — the permissive default
[FOUNDATION.md](../../docs/FOUNDATION.md) law 8 forbids.
-/
theorem authority_effect_applies_when_nothing_refuses {policy : StepPolicy}
    {state : MachineState} {d : AccessDescriptor} {prospective : Option MemoryEvent}
    (h : refusalOf policy state d prospective = Option.none) :
    (state.memory.applyAuthorityEffect? d.context d.authorityEffect).isSome := by
  unfold refusalOf at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · next hnone => simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using hnone

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
**The classes `performAccess` records outside `refusalOf` are declared too.**

`refusalOf_class_declared` covers the class `refusalOf` returns. `performAccess`
appends violations at three further points — an undeclared address space, the
outcome's own violation, and the branch where the declared authority effect does not
apply — and review pointed out that the last of those is outside that theorem's
reach, which matters because that branch is the one actually doing the refusing: with
`refusalOf`'s authority clause deleted the whole build stays green, because the
fallback still records and still commits nothing.

Two of the three are settled here. The address-space and authority classes are the
transition's own, so `StepPolicy.violationClassesDeclared` covers them by the same
route `refusalOf_class_declared` takes.

The third is neither covered nor reachable, and the second half of that is a
correction. This docstring used to say `AccessOutcome.violation?` "is supplied by the
profile's machine oracle, so nothing in this layer bounds its class". The oracle
cannot supply it: `Oracle.answer` returns a `CompleteCommitted`, never an
`AccessOutcome`, and `performAccess`'s two call sites build `.completed` and
`.faulted`. `AccessOutcome.denied` has no producer anywhere in `Grass/` or `Tests/`,
so the branch that reads `outcome.violation?` is dead code and the open item recorded
against it named a component with no way to reach it. What is owed is smaller than
what was recorded: either a producer for `.denied` or its deletion.
-/
theorem transition_own_classes_declared (policy : StepPolicy) :
    policy.profile.vocabulary.auditViolationClasses.Recognizes
      AuditViolationClass.wrongAddressSpace ∧
    policy.profile.vocabulary.auditViolationClasses.Recognizes
      AuditViolationClass.authorityEffectRefused :=
  ⟨policy.violationClassesDeclared _
    (AuthorityProvider.mem_emittedClasses_of_transition (by decide)),
   policy.violationClassesDeclared _
    (AuthorityProvider.mem_emittedClasses_of_transition (by decide))⟩

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
            match applyLedgerEffect? state.obligations state.contexts.domain d.context
                d.ledgerEffect with
            | Option.none =>
                -- Unreachable, for the same reason the authority branch below is:
                -- `refusalOf` decided applicability with `LedgerEffectApplicable`, and
                -- `ledgerEffectApplicable_iff_isSome` says that is exactly this
                -- function succeeding. `ledger_effect_applies_when_nothing_refuses` is
                -- the proof. Recorded rather than falling back to the unchanged ledger,
                -- because a fallback would commit an access whose declared duty did not
                -- appear.
                { state with
                  violations :=
                    state.violations.append (violationOf d .obligationNotAuthorized) }
            | some ledger =>
            match state.memory.applyAuthorityEffect? d.context d.authorityEffect with
            | Option.none =>
                -- Unreachable: `refusalOf` returned `none`, and its authority clause
                -- runs this same function against this same state, which
                -- `authority_effect_applies_when_nothing_refuses` is the proof of.
                -- Recorded rather than silently falling back to the unchanged map,
                -- because a fallback here would commit an access whose declared
                -- lend did not happen.
                { state with
                  violations :=
                    state.violations.append (violationOf d .authorityEffectRefused) }
            | some lent =>
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
                -- The declared authority changes land on the pre-access map, which
                -- is the map `refusalOf` checked them against, and the bytes are
                -- written on top. `MemoryState.commit` touches bytes only, so the
                -- two commute; doing it the other way would check a lend against
                -- one map and apply it to another.
                memory := lent.commit d (outcome.committed?.bind Committed.written)
                obligations := ledger }

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
      match policy.oracle.answer state d with
      | Option.none =>
          -- The machine cannot complete an access the profile admitted. Recorded
          -- and stopped, exactly like a denial: an oracle that cannot supply the
          -- bytes a store declared is a machine description that does not match
          -- the access, and accepting a short answer as success was how a
          -- malformed answer became a successful execution.
          { state with
            violations :=
              state.violations.append (violationOf d .machineAnswerIncomplete) }
      | some complete =>
          let next := performAccess policy state d (.completed complete) contextKind cause
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
  `readCommitted` and `writeCommitted` bytes. Separate counts, because a faulting
  read-modify-write can have observed its operand and stored nothing. -/
  | before (index : Fin sequence.substeps.length) (fault : FaultClassId)
      (readCommitted writeCommitted : Nat)

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
  | .before index fault reads writes =>
      match sequence.visibleEffects? index.val with
      | Option.none => state
      | some survivors =>
          let survived := runAccesses policy state survivors contextKind cause
          -- A denial among the survivors stops the operation, exactly as it does
          -- in `runAccesses`. The faulting substep is never reached, so it
          -- neither commits nor records its fault.
          --
          -- This branch used to omit the check and perform the faulting substep's
          -- access unconditionally, which meant a refused earlier substep was
          -- followed by a committed later write: the continue-after-denial
          -- behaviour `runAccesses` exists to prevent, surviving on the branch
          -- `runAccesses_stops_at_refusal` does not reach. Review found it with a
          -- machine-checked counterexample. `runStep_stops_at_refusal` is the
          -- theorem that now covers this branch.
          if survived.violations.recordCount ≠ state.violations.recordCount then
            survived
          else
            -- The fault is recorded before the branch on what kind of substep
            -- faulted, so no branch can discard it. An earlier version took the
            -- fault as an argument and dropped it wherever the faulting substep
            -- was not an access -- which is exactly the compute substep a divide
            -- faults on, so the one case the `compute` constructor exists for was
            -- the one that lost its fault.
            let faulted :=
              { survived with
                faults := survived.faults ++
                  [{ fault := fault, context := context, cause := cause
                     substep := index.val }] }
            match sequence.substeps[index.val]? with
            | some (.access d) =>
                -- The faulting substep's own partial commit is governed by the
                -- sequence's visibility rule, like every other substep's.
                -- Committing it unconditionally meant a `transactional` sequence
                -- discarded its completed substeps and kept the faulting one's
                -- prefix, which is the reverse of what `transactional` declares.
                if sequence.faultingEffectVisible then
                  match policy.oracle.answer faulted d with
                  | Option.none =>
                      { faulted with
                        violations := faulted.violations.append
                          (violationOf d .machineAnswerIncomplete) }
                  | some complete =>
                      performAccess policy faulted d
                        (.faulted fault (complete.committed.truncate reads writes))
                        contextKind cause
                else faulted
            | _ => faulted

/--
The fault-visibility rule this sequence names, if the profile has not registered
it.

Two registries, not one: a target theorem for cross-substep atomicity is a
different claim from a profile's own visibility rule, and sharing a namespace
would let either name satisfy the other. `priorEffectsVisible` names nothing and
claims nothing, which `FaultVisibility.RequiresJustification` is the predicate
for.
-/
def StepPolicy.unregisteredOnFaultRule? (policy : StepPolicy) (sequence : SubstepSequence) :
    Option Name :=
  match sequence.onFault with
  | .priorEffectsVisible => Option.none
  | .transactional justification =>
      if policy.profile.vocabulary.atomicityJustifications.Recognizes justification then
        Option.none
      else some justification
  | .profileSpecific rule =>
      if policy.profile.vocabulary.faultVisibilityRules.Recognizes rule then Option.none
      else some rule

/-- **A rule that claims nothing needs no registration.**

One direction only: `priorEffectsVisible` is never reported. It does not say that
the other two always are, and it does not mention
`FaultVisibility.RequiresJustification` — an earlier version of this docstring said
this was "exactly the one this never reports", which claims a uniqueness the
statement does not have, and tied it to a predicate the statement never names.

Not a `simp` lemma: its left-hand side is fully general and its hypothesis would
have to be discharged from context at every occurrence. -/
theorem unregisteredOnFaultRule?_priorEffectsVisible (policy : StepPolicy)
    (sequence : SubstepSequence) (h : sequence.onFault = .priorEffectsVisible) :
    policy.unregisteredOnFaultRule? sequence = Option.none := by
  unfold StepPolicy.unregisteredOnFaultRule?
  rw [h]

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
        else match sequence.accesses.findSome?
            (fun d => policy.profile.vocabulary.whyNotAdmitted? d) with
        | some reason => .rejected (.accessNotAdmitted reason)
        | Option.none =>
          -- Every access must name the context actually running the step. The
          -- event's identity comes from the descriptor and its kind from here, so
          -- without this the two disagree and the race check keys on the
          -- descriptor's word for it.
          match sequence.accesses.find? (fun d => d.context != context) with
          | some d => .rejected (.contextMismatch d.context context)
          | Option.none =>
          if ! decide (state.KindAgrees context contextKind) then
            .rejected (.contextKindMismatch context contextKind
              ((state.contexts.lookup context).getD contextKind))
          else
          -- A compute substep has no descriptor, so `Admits` never checks its
          -- declared faults against the vocabulary. This is the sibling clause.
          match sequence.substeps.findSome? (fun sub =>
              match sub with
              | .access _ => Option.none
              | .compute faults =>
                  faults.find? (fun f =>
                    ! decide (policy.profile.vocabulary.faultClasses.Recognizes f))) with
          | some fault => .rejected (.computeFaultNotRecognized fault)
          | Option.none =>
          -- The operation's own fault declaration, cross-checked against the
          -- substeps below it and against the vocabulary. Both directions matter:
          -- a substep that may raise a class the operation does not declare makes
          -- the declaration a lie, and a class the operation declares that no
          -- registry recognizes is a name nothing admitted. Neither was checked.
          -- An absent facet is *not* a declaration of no faults: law 8 again, and
          -- whether the profile may leave it absent is `Closes`'s question, not
          -- this one. There is simply nothing to cross-check.
          match operation.facets.faults.bind (fun declared =>
              declared.find? (fun f =>
                ! decide (policy.profile.vocabulary.faultClasses.Recognizes f))) with
          | some fault => .rejected (.operationFaultNotRecognized fault)
          | Option.none =>
          match operation.facets.faults.bind (fun declared =>
              sequence.substeps.findSome? (fun sub =>
                sub.faults.find? (fun f => !declared.contains f))) with
          | some fault => .rejected (.operationFaultsIncomplete fault)
          | Option.none =>
          -- Checked here rather than in `visibleEffects?`, which only runs on a
          -- faulting path: a sequence naming an unregistered rule and not faulting
          -- ran and minted its events with the claim unexamined.
          match policy.unregisteredOnFaultRule? sequence with
          | some rule => .rejected (.onFaultRuleNotRegistered rule)
          | Option.none =>
          -- The operation's ordering declaration against the substeps below it.
          -- Skipped when the facet is absent: absence is not a declaration of
          -- `plain`, and whether it may be absent is `Closes`'s question.
          match operation.facets.ordering.bind (fun declared =>
              (sequence.accesses.find? (fun d => d.ordering != declared)).map
                (fun d => (declared, d.ordering))) with
          | some (declared, requested) =>
              .rejected (.operationOrderingDisagrees declared requested)
          | Option.none =>
          -- And against the vocabulary directly. Checking it only through the
          -- accesses is vacuous for an access-free sequence, and a `.compute`-only
          -- operation declaring an unregistered profile-specific mode stepped.
          match operation.facets.ordering.bind (fun declared =>
              if ¬ policy.profile.vocabulary.AdmitsOrder declared.order then
                declared.order.profileName?
              else if ¬ policy.profile.vocabulary.AdmitsScope declared.scope then
                declared.scope.profileName?
              else Option.none) with
          | some name => .rejected (.operationOrderingNotRegistered name)
          | Option.none =>
          match faultAt sequence with
          | .none =>
              .ran (runStep policy (state.noteContext context contextKind) sequence context
                contextKind cause .none)
          | .before index fault reads writes =>
              if ! decide (fault ∈ sequence.substeps[index].faults) then
                .rejected (.faultClassNotDeclared fault)
              else if ! (match sequence.substeps[index].descriptor? with
                  | some d =>
                      decide (reads ≤ (if d.intent.reads then d.range.size else 0) ∧
                        writes ≤ (if d.intent.writes then d.range.size else 0))
                  | Option.none => decide (reads = 0 ∧ writes = 0)) then
                .rejected .faultCommitOutOfRange
              else if sequence.faultingEffectVisible &&
                  ! (sequence.substeps[index].descriptor?.elim true
                    (fun d => d.ledgerEffect.isEmpty)) then
                .rejected .faultWithUndeclaredLedgerEffect
              else if sequence.faultingEffectVisible &&
                  ! (sequence.substeps[index].descriptor?.elim true
                    (fun d => d.authorityEffect.isEmpty)) then
                .rejected .faultWithUndeclaredAuthorityEffect
              else
                match sequence.visibleEffects? index.val with
                | Option.none => .rejected .visibilityRuleUnknown
                | some _ =>
                    .ran (runStep policy (state.noteContext context contextKind) sequence
                      context contextKind cause (.before index fault reads writes))

/-! ## The transition invariants

These are the properties the docstrings elsewhere point at. Under the rule in
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §3.10, a comment saying "ensures",
"prevents", "cannot", "only", or "preserves" must name one of these or a type;
otherwise it is an intended invariant or an open obligation and says so. -/

/--
**A refused access changes nothing but the violation ledger.**

Every refusal path `refusalOf` gathers. `refusalOf` gathers those — the state's own denial,
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
    (cause : EventCause) (complete : CompleteCommitted d)
    (hanswer : policy.oracle.answer state d = some complete)
    (hrefused :
      (performAccess policy state d (.completed complete)
        contextKind cause).violations.recordCount ≠ state.violations.recordCount) :
    runAccesses policy state (d :: rest) contextKind cause =
      performAccess policy state d (.completed complete) contextKind cause := by
  rw [runAccesses, hanswer]
  simp [hrefused]

/--
**An access the machine cannot complete is recorded and stops the operation.**

The other way `runAccesses` refuses. `Oracle.answer` returning `none` means the
machine cannot fill an access the profile admitted, and accepting a short answer
as success is how a malformed answer became a successful execution: an oracle
supplying no bytes for a nonempty store produced a `completed` outcome that
`AccessOutcome.status` relabelled `partialCommit 0 0`, committing nothing while
later substeps carried on. Review type-checked that against the seam fixture.
-/
theorem runAccesses_stops_when_the_machine_cannot_answer (policy : StepPolicy)
    (state : MachineState) (d : AccessDescriptor) (rest : List AccessDescriptor)
    (contextKind : ContextKind) (cause : EventCause)
    (hanswer : policy.oracle.answer state d = Option.none) :
    runAccesses policy state (d :: rest) contextKind cause =
      { state with
        violations :=
          state.violations.append (violationOf d .machineAnswerIncomplete) } := by
  rw [runAccesses, hanswer]

/--
**A denial stops the operation on the faulting path too.**

`runAccesses_stops_at_refusal` covers the access list. It does not cover
`runStep`'s faulting branch, which runs the survivors and then performs the
faulting substep's own access — and that branch used to perform it whether or not
a survivor had been refused. The result was continue-after-denial behaviour
surviving in the one place no theorem reached: a refused substep followed by a
committed write, with the denial duly recorded beside it. Local adversarial review
found it with a machine-checked counterexample, on code that had already merged.

`docs/FOUNDATION.md` law 8 is the rule it broke. `docs/MEMORY_MODEL.md` §1 lets a
profile say which *completed* effects survive a fault; a denied substep did not
complete, so nothing licenses what follows it.
-/
theorem runStep_stops_at_refusal (policy : StepPolicy) (state : MachineState)
    (sequence : SubstepSequence) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) (index : Fin sequence.substeps.length) (fault : FaultClassId)
    (reads writes : Nat) (survivors : List AccessDescriptor)
    (hvisible : sequence.visibleEffects? index.val = some survivors)
    (hrefused : (runAccesses policy state survivors contextKind cause).violations.recordCount
      ≠ state.violations.recordCount) :
    runStep policy state sequence context contextKind cause (.before index fault reads writes) =
      runAccesses policy state survivors contextKind cause := by
  show (match sequence.visibleEffects? index.val with
    | Option.none => state
    | some survivors =>
        let survived := runAccesses policy state survivors contextKind cause
        if survived.violations.recordCount ≠ state.violations.recordCount then survived
        else
          let faulted :=
            { survived with
              faults := survived.faults ++
                [({ fault := fault, context := context, cause := cause
                    substep := index.val } : RaisedFault)] }
          match sequence.substeps[index.val]? with
          | some (.access d) =>
              if sequence.faultingEffectVisible then
                match policy.oracle.answer faulted d with
                | Option.none =>
                    { faulted with
                      violations := faulted.violations.append
                        (violationOf d .machineAnswerIncomplete) }
                | some complete =>
                    performAccess policy faulted d
                      (.faulted fault (complete.committed.truncate reads writes))
                      contextKind cause
              else faulted
          | _ => faulted) = _
  rw [hvisible]
  dsimp only
  rw [if_pos hrefused]

/-- A denial on the faulting path records no fault, because the faulting substep
was never reached. The complement of `runStep_records_the_fault`'s `hreached`. -/
theorem runStep_records_no_fault_after_refusal (policy : StepPolicy) (state : MachineState)
    (sequence : SubstepSequence) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) (index : Fin sequence.substeps.length) (fault : FaultClassId)
    (reads writes : Nat) (survivors : List AccessDescriptor)
    (hvisible : sequence.visibleEffects? index.val = some survivors)
    (hrefused : (runAccesses policy state survivors contextKind cause).violations.recordCount
      ≠ state.violations.recordCount) :
    (runStep policy state sequence context contextKind cause
      (.before index fault reads writes)).faults =
      (runAccesses policy state survivors contextKind cause).faults := by
  rw [runStep_stops_at_refusal policy state sequence context contextKind cause index fault
    reads writes survivors hvisible hrefused]

/--
The refusal path `refusalOf` does not gather.

An access naming an address space the profile never declared is refused by the
space lookup, before `refusalOf` runs, so
`refused_preserves_everything_but_the_ledger` excludes it by hypothesis. Review
pointed out that its docstring claimed *every* refusal path while this one sat
outside. `unknown_space_preserves_everything_but_the_ledger` is that path's proof.

Two is still not all of them: `no_event_records_nothing` is the third, and review
found the sentence claiming a pair sufficed.

`step` rejects an access the profile does not admit before reaching here, so the
branch is not reachable through `step` today. It is proved anyway: `performAccess`
is public, and unreachable-by-construction-elsewhere is not the same as proved
harmless.
-/
theorem unknown_space_preserves_everything_but_the_ledger (policy : StepPolicy)
    (state : MachineState) (d : AccessDescriptor) (outcome : AccessOutcome d)
    (contextKind : ContextKind) (cause : EventCause)
    (hspace : policy.profile.vocabulary.addressSpaces.find? d.space = Option.none) :
    performAccess policy state d outcome contextKind cause =
      { state with
        violations := state.violations.append (violationOf d .wrongAddressSpace) } := by
  unfold performAccess
  rw [hspace]

/--
The branch that refuses nothing and records nothing.

When `MemoryEvent.ofOutcome` yields no event and the outcome carries no violation,
`performAccess` returns the state untouched without consulting `refusalOf` at all.
So this is a third path distinct from the two theorems above, and review found the
docstring there claiming a pair covered every refusal.

`MemoryEvent.ofOutcome` returns `none` for a committed outcome in two cases, and
neither is reachable from `step`. One is an *inert* access — one that neither reads
nor writes — which `AccessDescriptor.WellFormedIn.notInert` makes unadmittable. The
other is a `space` whose identity disagrees with `d.provenance.space`, which
`ValidMemoryEvent.WellFormed.spaceAgreesWithProvenance` requires and which `step`
cannot produce because it resolves the space *from* the provenance. An earlier version
of this docstring named only the first and said "only in that case"; the second
arrived with the well-formedness field and the docstring did not.

The theorem exists anyway, for the reason
`unknown_space_preserves_everything_but_the_ledger` gives: `performAccess` is
public, and unreachable-by-construction-elsewhere is not proved harmless. The space
case is the less comfortable of the two, because a disagreement becomes a silent
no-op rather than a violation; `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records
what turning it into a rejection would take.

Worth naming precisely, because it is the one place a *denial* goes unrecorded: an
inert access over dead provenance is refused by `denialOf` and this branch returns
before anything asks. Nothing commits either, so `docs/MEMORY_MODEL.md` §8's ban on
erasing a violation is not broken by any reachable execution — but the branch is
why `runStep`'s guard, which watches the violation count, cannot see it.
-/
theorem no_event_records_nothing (policy : StepPolicy) (state : MachineState)
    (d : AccessDescriptor) (outcome : AccessOutcome d) (contextKind : ContextKind)
    (cause : EventCause) (space : AddressSpace)
    (hspace : policy.profile.vocabulary.addressSpaces.find? d.space = some space)
    (hnoevent : MemoryEvent.ofOutcome state.eventSupply.fresh.1 contextKind cause space d
      outcome = Option.none)
    (hnoviolation : outcome.violation? = Option.none) :
    performAccess policy state d outcome contextKind cause = state := by
  unfold performAccess
  rw [hspace]
  simp only []
  rw [hnoevent, hnoviolation]

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
    (hledger : ¬ LedgerEffectApplicable state.obligations state.contexts.domain d.context
      d.ledgerEffect) :
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

/--
**An access that declares no authority change makes none.**

`docs/FOUNDATION.md` law 6 forbids ambient provider choice, and this is the same
reading applied to authority: a grant may not appear or disappear because an access
happened, only because an access said it would. Every other fact about the authority
effect is a point check through a fixture's `step`; this one is over an arbitrary
policy, state, descriptor and outcome, which is what makes it a law about the
transition rather than about six operations someone wrote.

The proof is the whole reason `MemoryState.grantEntries_write` and
`Grass.Memory.grantEntries_commit` exist: the committing branch applies the declared
effect and then writes bytes on top, so "no declaration" has to survive the write as
well as the empty effect.
-/
theorem performAccess_preserves_authority_of_no_effect (policy : StepPolicy)
    (state : MachineState) (d : AccessDescriptor) (outcome : AccessOutcome d)
    (contextKind : ContextKind) (cause : EventCause) (h : d.authorityEffect = []) :
    (performAccess policy state d outcome contextKind cause).memory.grantEntries =
      state.memory.grantEntries := by
  unfold performAccess
  split
  · rfl
  · split
    · split <;> rfl
    · split
      · rfl
      · split
        · rfl
        · rw [h, MemoryState.applyAuthorityEffect?_nil]
          exact Grass.Memory.grantEntries_commit _ _ _

/--
**And a whole run of such accesses makes none.**

The form a straight-line argument uses: an operation whose descriptors all declare
nothing leaves the authority map exactly as it found it, however many substeps it has
and wherever it stops — at the end, at a denial, or at an oracle that could not
answer.

`runStep` is not covered, because its faulting branches run
`SubstepSequence.visibleEffects?`, and nothing in this layer relates a survivor list
to the sequence's own accesses; without that the hypothesis cannot be discharged for
the surviving prefix. That is a missing lemma rather than a missing law, and
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records it.
-/
theorem runAccesses_preserves_authority_of_no_effects (policy : StepPolicy)
    (contextKind : ContextKind) (cause : EventCause) :
    ∀ (accesses : List AccessDescriptor) (state : MachineState),
      (∀ d ∈ accesses, d.authorityEffect = []) →
        (runAccesses policy state accesses contextKind cause).memory.grantEntries =
          state.memory.grantEntries := by
  intro accesses
  induction accesses with
  | nil => intro state _; rfl
  | cons d rest ih =>
    intro state hall
    have hhead : d.authorityEffect = [] := hall d List.mem_cons_self
    have htail : ∀ x ∈ rest, x.authorityEffect = [] :=
      fun x hx => hall x (List.mem_cons_of_mem _ hx)
    unfold runAccesses
    cases hanswer : policy.oracle.answer state d with
    | none => rfl
    | some complete =>
      simp only []
      by_cases hstop : (performAccess policy state d (.completed complete) contextKind
          cause).violations.recordCount = state.violations.recordCount
      · rw [if_pos hstop]
        exact (ih _ htail).trans
          (performAccess_preserves_authority_of_no_effect policy state d _ contextKind
            cause hhead)
      · rw [if_neg hstop]
        exact performAccess_preserves_authority_of_no_effect policy state d _ contextKind
          cause hhead

/--
**And a whole step makes none**, however it faults.

The law `runAccesses_preserves_authority_of_no_effects` could not reach when it was
written: the faulting branches run `SubstepSequence.visibleEffects?`, and nothing
related its answer to the sequence's own accesses, so a hypothesis quantified over
`sequence.accesses` could not be discharged for the survivors.
`SubstepSequence.mem_accesses_of_mem_visibleEffects?` and `mem_accesses_of_substep`
are the two lemmas that were missing — the survivors are a prefix of the sequence's
accesses, and the faulting substep's own descriptor is one of them.

With them, this holds for every fault plan: no plan, a fault whose visibility rule
belongs to a profile (where the step does nothing at all), a fault whose survivors
stop at a denial, and a fault whose own substep commits a partial write.
-/
theorem runStep_preserves_authority_of_no_effects (policy : StepPolicy)
    (state : MachineState) (sequence : SubstepSequence) (context : ContextId)
    (contextKind : ContextKind) (cause : EventCause) (plan : FaultPlan sequence)
    (h : ∀ d ∈ sequence.accesses, d.authorityEffect = []) :
    (runStep policy state sequence context contextKind cause plan).memory.grantEntries =
      state.memory.grantEntries := by
  unfold runStep
  split
  · exact runAccesses_preserves_authority_of_no_effects policy contextKind cause _ state h
  · next index fault reads writes =>
    split
    · rfl
    · next survivors hvisible =>
      have hsurvivors : ∀ d ∈ survivors, d.authorityEffect = [] :=
        SubstepSequence.forall_visibleEffects?_of_forall_accesses hvisible h
      have hrun : (runAccesses policy state survivors contextKind cause).memory.grantEntries
          = state.memory.grantEntries :=
        runAccesses_preserves_authority_of_no_effects policy contextKind cause _ state
          hsurvivors
      dsimp only
      split
      · exact hrun
      · split
        · next d hsubstep =>
          have hd : d.authorityEffect = [] :=
            h d (SubstepSequence.mem_accesses_of_substep hsubstep)
          split
          · split
            · exact hrun
            · exact (performAccess_preserves_authority_of_no_effect policy _ d _ contextKind
                cause hd).trans hrun
          · exact hrun
        · exact hrun

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
      · split
        · exact AuditViolationLedger.extends_append _ _
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
    rw [runAccesses]
    split
    · exact AuditViolationLedger.extends_append _ _
    · rename_i complete _
      have hp := performAccess_extends_violations policy state d
        (.completed complete) contextKind cause
      dsimp only
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
    · dsimp only
      repeat' split
      all_goals
        first
          | exact runAccesses_extends_violations _ _ _ _ _
          | exact AuditViolationLedger.Extends.trans
              (runAccesses_extends_violations _ _ _ _ _)
              (performAccess_extends_violations _ _ _ _ _ _)
          | exact AuditViolationLedger.Extends.trans
              (runAccesses_extends_violations _ _ _ _ _)
              (AuditViolationLedger.extends_append _ _)

/-! ## The memory framing laws apply to this transition

`Grass/Memory/Apply.lean` proves framing over `MemoryState.commit`. Because
every committing access goes through `commit`, those laws are laws about this
transition. These theorems state that for `performAccess` and `runAccesses`, and
they exist because review found the earlier arrangement — two write paths, framing
proved about one of them, and prose claiming it covered both.

`runStep_frames_untouched` and `step_frames_untouched` carry this to the whole
operation, and they are not `runAccesses_frames_untouched` restated. `runStep`'s
faulting branch runs the survivors, which `visibleEffects?` chose and which
*exclude* the faulting substep, and then performs that substep's access itself — so
framing over the survivor list alone says nothing about the byte that access
writes. A second review round found an earlier comment here claiming otherwise, and
a consumer following it would have had an unsound argument. The hypothesis
quantifies over `sequence.accesses`, which `mem_accesses_of_visibleEffects?` shows
contains every survivor and which contains the faulting substep's descriptor. -/

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
  have hfits : Grass.Memory.WrittenFits d (outcome.committed?.bind Committed.written) :=
    fun bytes hb => by
      cases hc : outcome.committed? with
      | none => rw [hc] at hb; exact absurd hb (by simp)
      | some c =>
        rw [hc] at hb
        simp only [Option.bind_some] at hb
        exact c.writtenFits bytes hb
  unfold performAccess
  repeat' split
  all_goals
    first
      | rfl
      | (rename_i hlent
         exact (Grass.Memory.cellAt?_commit_of_untouched _ d hfits h).trans
           (MemoryState.cellAt?_applyAuthorityEffect? hlent id offset))
      | exact Grass.Memory.cellAt?_commit_of_untouched state.memory d hfits h

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
    show ((match policy.oracle.answer state d with
            | Option.none =>
                { state with
                  violations :=
                    state.violations.append (violationOf d .machineAnswerIncomplete) }
            | some complete =>
                if (performAccess policy state d (.completed complete)
                      contextKind cause).violations.recordCount =
                    state.violations.recordCount then
                  runAccesses policy (performAccess policy state d (.completed complete)
                    contextKind cause) rest contextKind cause
                else performAccess policy state d (.completed complete)
                  contextKind cause) : MachineState).memory.cellAt? id offset = _
    split
    · rfl
    · rename_i complete _
      have hhead := performAccess_frames_untouched policy state d
        (AccessOutcome.completed complete) contextKind cause
        (hall d List.mem_cons_self)
      split
      · rw [runAccesses_frames_untouched policy rest _ contextKind cause
          (fun x hx => hall x (List.mem_cons_of_mem _ hx))]
        exact hhead
      · exact hhead

/--
**A whole step frames every cell no access it declares touches.**

The `step`-level theorem `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 recorded as
owed, and which four documents had claimed already existed before review corrected
them.

Why it is not just `runAccesses_frames_untouched`. `runStep`'s faulting branch runs
the survivors, which `visibleEffects?` chose and which *exclude* the faulting
substep, and then performs that substep's own access separately. Framing
established over the survivor list therefore says nothing about the byte the
faulting access writes, and a consumer following the old prose to
`runAccesses_frames_untouched` would have had an unsound argument. The hypothesis
here quantifies over `sequence.accesses`, which
`SubstepSequence.mem_accesses_of_visibleEffects?` shows contains every survivor and
which contains the faulting substep's descriptor too.
-/
theorem runStep_frames_untouched (policy : StepPolicy) (state : MachineState)
    (sequence : SubstepSequence) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) (plan : FaultPlan sequence) {id : AllocId} {offset : Nat}
    (hall : ∀ d ∈ sequence.accesses, ¬ (d.provenance.root = id ∧ d.range.Covers offset)) :
    (runStep policy state sequence context contextKind cause plan).memory.cellAt? id offset =
      state.memory.cellAt? id offset := by
  unfold runStep
  split
  · exact runAccesses_frames_untouched policy _ _ _ _ hall
  · rename_i index fault reads writes
    split
    · rfl
    · rename_i survivors hvisible
      have hsurv : ∀ d ∈ survivors, ¬ (d.provenance.root = id ∧ d.range.Covers offset) :=
        fun d hd => hall d (SubstepSequence.mem_accesses_of_visibleEffects? hvisible hd)
      have hrun := runAccesses_frames_untouched policy survivors state contextKind cause hsurv
      dsimp only
      split
      · exact hrun
      · split
        · rename_i d hsub
          have hmem : Substep.access d ∈ sequence.substeps := by
            obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hsub
            exact heq ▸ List.getElem_mem hlt
          have hd : d ∈ sequence.accesses :=
            SubstepSequence.mem_accesses_of_descriptor? hmem rfl
          split
          · split
            · exact hrun
            · rw [performAccess_frames_untouched policy _ d _ contextKind cause (hall d hd)]
              exact hrun
          · exact hrun
        · exact hrun

/--
**A whole `step` frames every cell no access it declares touches.**

The form a consumer wants: `step` rather than `runStep`, so the rejection paths are
included and a caller reasons about the operation it actually ran. A rejected step
produces no state at all, so there is nothing to frame; a step that ran frames
through `runStep_frames_untouched`.
-/
theorem step_frames_untouched (policy : StepPolicy) (state : MachineState)
    (operation : SomeOperation) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause)
    (faultAt : (sequence : SubstepSequence) → FaultPlan sequence) (final : MachineState)
    {id : AllocId} {offset : Nat}
    (h : step policy state operation context contextKind cause faultAt = .ran final)
    (hall : ∀ sequence, operation.facets.substeps? = some sequence →
      ∀ d ∈ sequence.accesses, ¬ (d.provenance.root = id ∧ d.range.Covers offset)) :
    final.memory.cellAt? id offset = state.memory.cellAt? id offset := by
  unfold step at h
  split at h
  · exact absurd h (by simp)
  · rename_i hfacets
    split at h
    · exact absurd h (by simp)
    · rename_i sequence hseq
      have hacc := hall sequence hseq
      -- Every rejection branch is `.rejected _ = .ran final`, which `cases`
      -- discharges outright; what survives is the branch that ran.
      repeat' split at h
      all_goals cases h
      all_goals
        rw [runStep_frames_untouched policy _ sequence context contextKind cause _ hacc,
          MachineState.noteContext_memory]

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

`hreached` is required and is not a weakening. If a surviving substep was refused,
the operation stopped there and the faulting substep was never reached, so there
is no fault of its to record; `runStep_stops_at_refusal` is that case. The
guarantee is that a fault the operation actually reached is never discarded, not
that a fault is invented for a substep that never ran.
-/
theorem runStep_records_the_fault (policy : StepPolicy) (state : MachineState)
    (sequence : SubstepSequence) (context : ContextId) (contextKind : ContextKind)
    (cause : EventCause) (index : Fin sequence.substeps.length) (fault : FaultClassId)
    (reads writes : Nat) (survivors : List AccessDescriptor)
    (hvisible : sequence.visibleEffects? index.val = some survivors)
    (hreached : (runAccesses policy state survivors contextKind cause).violations.recordCount =
      state.violations.recordCount) :
    ∃ record ∈ (runStep policy state sequence context contextKind cause
      (.before index fault reads writes)).faults, record.fault = fault := by
  show ∃ record ∈ (match sequence.visibleEffects? index.val with
    | Option.none => state
    | some survivors =>
        let survived := runAccesses policy state survivors contextKind cause
        if survived.violations.recordCount ≠ state.violations.recordCount then survived
        else
          let faulted :=
            { survived with
              faults := survived.faults ++
                [({ fault := fault, context := context, cause := cause
                    substep := index.val } : RaisedFault)] }
          match sequence.substeps[index.val]? with
          | some (.access d) =>
              if sequence.faultingEffectVisible then
                match policy.oracle.answer faulted d with
                | Option.none =>
                    { faulted with
                      violations := faulted.violations.append
                        (violationOf d .machineAnswerIncomplete) }
                | some complete =>
                    performAccess policy faulted d
                      (.faulted fault (complete.committed.truncate reads writes))
                      contextKind cause
              else faulted
          | _ => faulted).faults, record.fault = fault
  rw [hvisible]
  simp only [hreached, ne_eq, not_true_eq_false, if_false]
  repeat' split
  all_goals
    first
      | (rw [performAccess_preserves_faults]
         exact ⟨{ fault := fault, context := context, cause := cause, substep := index.val },
           by simp, rfl⟩)
      | exact ⟨{ fault := fault, context := context, cause := cause, substep := index.val },
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
