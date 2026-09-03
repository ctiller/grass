import Grass.Memory.Audit
import Grass.Memory.Access
import Grass.Obligation.Core

/-!
# Memory profiles

A profile is what makes an open vocabulary safe.

Every nominal name in this layer — address space, memory type, fault class,
allocation source, provenance step kind, audit violation class, obligation kind —
is open, so a platform or device profile can introduce its own without editing the
vocabulary. On its own that is a silent-acceptance path: a misspelled
address-space name is a different, perfectly usable address space, and nothing
would notice.

`docs/FOUNDATION.md` law 8 does not permit that: "unknown instructions, targets,
effects, encodings, or API behavior are rejected, not approximated as no-ops."
`docs/MEMORY_MODEL.md` §9 says where the rejection lives: "Unimplemented behavior
is rejected by profile applicability, never modeled as harmless."

`NameRegistry` is that mechanism. A profile lists the names it admits, and
`recognize?` returns an `Option`, so a consumer either holds a `Recognized` value
carrying evidence or has to handle the `none`. There is no way to obtain evidence
for a name the profile never listed.

**Every registry here is consulted.** A registry nothing dispatches through is
documentation, not a mechanism, and two of these were exactly that until
`Admits` was extended to check the obligation kinds an access creates and the
violation classes a profile may record. Open extensibility does not by itself
require a registry — the existential operation package carries its own evidence
(`Grass/Op/Facets.lean`) — so a registry earns its place only by being checked.

## What this profile does not hold

Operation facets. A profile describes a target's *memory policy*; holding facets
would make the memory model depend on a closed operation universe and would force
`Memory` to import ISA definitions. `Grass/Op/Facets.lean` owns that seam, and
`Grass/Op/Step.lean` is where the two meet.

## The required proof package

`RequiredProofPackage` is the §10 list, as a record, shipped in M1 even though no
profile closes it until M10. An ISA author writing their first instruction can
then see the whole eventual obligation, and closure becomes a field-by-field
target rather than a discovery.

**What it is not.** Its fields are `Prop`s — propositions, not proofs of them —
so a profile can be built with every field set to `True`, or to `False`. It is a
checklist, and `PackageHolds` below is the only thing that turns it into a claim:
a consumer that demands `PackageHolds` demands proofs of all eleven. Nothing in
M1 demands it, because the statements those props should carry need machinery
that does not exist until M2 through M9. Treating a constructed `MemoryProfile`
as evidence that §10 has closed would be a mistake, and an earlier version of
this docstring invited exactly that reading.
-/

namespace Grass.Memory

open Grass.Core Grass.Obligation

/--
The names a profile admits on one axis of the open vocabulary.

A list rather than a predicate, because a profile's admitted set is finite,
enumerable, and reviewable — `docs/VALIDATION.md` expects it to appear in a
report — and because a predicate would let a profile admit an unbounded family
without anyone being able to read what it admitted.
-/
structure NameRegistry (α : Type) where
  /-- The names this profile admits. -/
  recognized : List α
deriving Repr

namespace NameRegistry

variable {α : Type} [DecidableEq α]

/-- `r.Recognizes x` holds when `x` is admitted. -/
def Recognizes (r : NameRegistry α) (x : α) : Prop := x ∈ r.recognized

instance (r : NameRegistry α) (x : α) : Decidable (r.Recognizes x) :=
  inferInstanceAs (Decidable (_ ∈ _))

/--
A name together with evidence that a profile admits it.

The `evidence` field is what makes this work: a `Recognized r` cannot be built
without a proof of `NameRegistry.Recognizes`, so a consumer holding one is
holding a name the profile really listed.
-/
structure Recognized (r : NameRegistry α) where
  /-- The admitted name. -/
  value : α
  /-- The profile admits it. -/
  evidence : r.Recognizes value

/--
Resolve a name against the registry.

Returns `none` for a name the profile does not admit. This is the rejection path
law 8 requires: a consumer must handle the `none`, and cannot proceed with an
unrecognized name by accident.
-/
def recognize? (r : NameRegistry α) (x : α) : Option (Recognized r) :=
  if h : r.Recognizes x then some ⟨x, h⟩ else Option.none

@[simp] theorem recognize?_eq_none_iff (r : NameRegistry α) (x : α) :
    r.recognize? x = Option.none ↔ ¬ r.Recognizes x := by
  unfold recognize?
  split <;> simp_all

@[simp] theorem recognize?_isSome_iff (r : NameRegistry α) (x : α) :
    (r.recognize? x).isSome ↔ r.Recognizes x := by
  unfold recognize?
  split <;> simp_all

/-- An unrecognized name yields nothing to work with. -/
theorem recognize?_of_not_recognizes {r : NameRegistry α} {x : α} (h : ¬ r.Recognizes x) :
    r.recognize? x = Option.none := by simp [h]

/-- The empty registry admits nothing. A profile that has declared no address
spaces admits no accesses, rather than admitting all of them. -/
def empty : NameRegistry α := ⟨[]⟩

omit [DecidableEq α] in
@[simp] theorem not_recognizes_empty (x : α) : ¬ (empty : NameRegistry α).Recognizes x := by
  simp [empty, Recognizes]

end NameRegistry

/--
The open vocabulary a profile admits.

Every registry must be listed. A profile with an empty registry on an axis whose
names are *entirely* the profile's admits nothing on that axis, which is the safe
direction.

That is not true of every registry here, and saying it flatly was wrong. The five
added for ordering and justifications gate only the profile-specific half of their
axis: with `orderingModes` empty, `AdmitsOrder .sequentiallyConsistent` still holds,
because §7.1 fixes the portable modes and there is nothing profile-local to declare
about them. The unqualified claim would have a reader believe an empty vocabulary
rejects every ordering request, and it does not.
-/
structure AdmittedVocabulary where
  /-- The address spaces this profile models, with their representations,
  memory types, and coherence. A table rather than a registry of names, because
  an access names a space and something other than the access has to decide what
  that space is; see `Grass/Memory/AddressSpace.lean`. -/
  addressSpaces : AddressSpaceTable
  /-- Architectural fault classes this profile models. -/
  faultClasses : NameRegistry FaultClassId
  /-- Allocation sources this profile models. -/
  allocationSources : NameRegistry AllocationSourceId
  /-- Provenance step kinds this profile models. -/
  provenanceStepKinds : NameRegistry ProvenanceStepKind
  /-- Audit violation classes this profile can record. -/
  auditViolationClasses : NameRegistry AuditViolationClass
  /-- Obligation kinds this profile's protocols use. -/
  obligationKinds : NameRegistry ObligationKindId
  /-- The kinds of authority grant this profile has. `GrantKind` is an open nominal
  name — `docs/MEMORY_MODEL.md` §3 names loans and frames and §5.1 names pins, and a
  target with a fourth is not this layer's business — so an operation minting one
  must mint one the profile declared.

  Not needed while only a fixture could issue a grant. It is needed now that
  `AccessDescriptor.authorityEffect` lets an operation issue one, because
  `MemoryState.AnyGrantOver` is kind-blind: a grant of an invented kind freezes bytes
  for every rule that asks whether anything is held. -/
  grantKinds : NameRegistry GrantKind
  /-- The obligation protocols this profile has. `ObligationProtocolId` is an open
  nominal name and `ProtocolAuthority.mintedBy` is public, total and unconditioned,
  so any module can mint authority for any protocol — review minted one from a string
  in a foreign file and discharged another family's duty with it, no violation
  recorded. Declaring the protocols is what makes a claim checkable at all. -/
  protocols : NameRegistry ObligationProtocolId
  /-- Ordering modes this profile owns, beyond the five portable ones.

  `docs/MEMORY_MODEL.md` §7.1 fixes the portable modes and allows a profile its
  own; a portable mode therefore needs no entry here and a profile-specific one
  does. Nothing registered these for several milestones, so an access could declare
  `MemoryOrder.profileSpecific` with any name at all and step. -/
  orderingModes : NameRegistry Name
  /-- Scopes this profile owns, beyond thread, process, device, and system. §7.1
  allows these on the same terms as the modes above. -/
  orderingScopes : NameRegistry Name
  /-- Rules under which this profile permits an access to read uninitialized
  bytes.

  `InitializationDemand.permitsUninitialized` names one, and nothing held the
  names, so an access read uninitialized bytes by declaring a string. This registry
  is where the name becomes checkable.

  **`docs/MEMORY_MODEL.md` §4 does not authorize the escape**, and an earlier
  version of this docstring said it did. §4's whole sentence on the subject is
  "Initialization is tracked at the granularity required to justify every read"; it
  states no violation and describes no profile exception. The escape is
  `InitializationDemand`'s own design, this registry gates its name, and neither is
  §4's. What §4 actually asks for — granularity sufficient to justify *every* read —
  is not delivered either: the demand is per-access, so a struct copy with three
  padding bytes must declare `permitsUninitialized` for the whole range, which turns
  the check off for every byte. §4.2 of the plan records that. -/
  initializationJustifications : NameRegistry Name
  /-- Target theorems this profile claims for cross-substep atomicity.

  `FaultVisibility.transactional` names one. Kept apart from the registry above
  rather than sharing a namespace with it: a rule permitting an uninitialized read
  is not a proof that a two-substep store is all-or-nothing, and one registry would
  let either name satisfy the other. Two facts in one carrier is the defect this
  layer removed from `AccessIntent.isDevice`. -/
  atomicityJustifications : NameRegistry Name
  /-- Fault-visibility rules this profile owns.

  `FaultVisibility.profileSpecific` names one. `SubstepSequence.visibleEffects?`
  already refuses to guess what such a rule says, but only on a faulting path — a
  sequence carrying an unregistered rule name and not faulting ran. -/
  faultVisibilityRules : NameRegistry Name
deriving Repr

namespace AdmittedVocabulary

/--
`vocabulary.WellFormed` holds when the vocabulary itself is coherent.

Without it the law-8 chain terminated in an unchecked record. A vocabulary could
declare `cpu.virtual` twice — once honestly and once with `repr := .symbolic` —
and `AddressSpaceTable.find?` returns the first match, so which version an access
was checked against depended on list order. Resolving a descriptor's space
through the profile is only a guarantee if the profile's own table is checked.

**And the three justification registries are pairwise disjoint**, which
`StepPolicy.vocabularyWellFormed` makes a construction obligation. `AdmittedVocabulary` keeps them
separate so that one name cannot satisfy another's claim: a rule permitting an
uninitialized read is not a proof that a two-substep store is all-or-nothing, and
§7.1's fault-visibility rules are a third thing again. Review
pointed out that nothing stopped a vocabulary listing one name in two of them, which
re-created at the profile level exactly the collapse the split was built to prevent —
the split was a convention, not a guarantee. It is a guarantee here, and it is
load-bearing because `StepPolicy.vocabularyWellFormed` makes it a construction
obligation: a profile that conflates two claims under one name cannot form a policy
at all.
-/
def WellFormed (vocabulary : AdmittedVocabulary) : Prop :=
  vocabulary.addressSpaces.WellFormed ∧
  vocabulary.atomicityJustifications.recognized.all
    (fun name => !decide (name ∈ vocabulary.faultVisibilityRules.recognized)) = true ∧
  vocabulary.initializationJustifications.recognized.all
    (fun name => !decide (name ∈ vocabulary.atomicityJustifications.recognized)) = true ∧
  vocabulary.initializationJustifications.recognized.all
    (fun name => !decide (name ∈ vocabulary.faultVisibilityRules.recognized)) = true

instance (vocabulary : AdmittedVocabulary) : Decidable vocabulary.WellFormed := by
  unfold AdmittedVocabulary.WellFormed AddressSpaceTable.WellFormed
  infer_instance

/--
`vocabulary.AdmitsOrder order` holds when the access may request that ordering.

A `profileSpecific` mode must be a name this profile registered: §7.1 says an
unsupported mapping is rejected, and a name no profile ever claimed is the clearest
case of one. The five portable modes pass without a registry entry.

**That exemption is this module's, not §7.1's**, and an earlier version of this
docstring credited §7.1 with it. §7.1's sentence is "Ordering requests use a
portable vocabulary *only where it has a proved target meaning*: relaxed, acquire,
release, acquire-release, sequentially consistent, and profile-specific modes." The
condition attaches to the portable names too. §7.1 fixes the vocabulary; it does not
make any of it unconditionally admissible, and this predicate lets a profile that
has proved nothing request `sequentiallyConsistent`.

What would close that is §7.1's refinement theorem — "Mapping a high-level order to
an ISA/API operation requires a refinement theorem" — which no profile here has and
which an ISA owner owes. `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 records it.
-/
def AdmitsOrder (vocabulary : AdmittedVocabulary) (order : MemoryOrder) : Prop :=
  match order.profileName? with
  | some name => vocabulary.orderingModes.Recognizes name
  | Option.none => True

instance (vocabulary : AdmittedVocabulary) (order : MemoryOrder) :
    Decidable (vocabulary.AdmitsOrder order) := by
  unfold AdmitsOrder
  split <;> infer_instance

/-- `vocabulary.AdmitsScope scope` holds when the access may claim that scope. The
same rule as `AdmitsOrder`, over §7.1's four portable scopes. -/
def AdmitsScope (vocabulary : AdmittedVocabulary) (scope : MemoryScope) : Prop :=
  match scope.profileName? with
  | some name => vocabulary.orderingScopes.Recognizes name
  | Option.none => True

instance (vocabulary : AdmittedVocabulary) (scope : MemoryScope) :
    Decidable (vocabulary.AdmitsScope scope) := by
  unfold AdmitsScope
  split <;> infer_instance

/-- A portable mode needs no registration. -/
theorem admitsOrder_of_isPortable {vocabulary : AdmittedVocabulary} {order : MemoryOrder}
    (h : order.IsPortable) : vocabulary.AdmitsOrder order := by
  unfold AdmitsOrder
  rw [MemoryOrder.profileName?_eq_none_iff_isPortable.mpr h]
  trivial

/-- And a portable scope needs none either. -/
theorem admitsScope_of_isPortable {vocabulary : AdmittedVocabulary} {scope : MemoryScope}
    (h : scope.IsPortable) : vocabulary.AdmitsScope scope := by
  unfold AdmitsScope
  rw [MemoryScope.profileName?_eq_none_iff_isPortable.mpr h]
  trivial

/--
**An admissible mode is portable or registered**, and there is no third way.

The direction that carries the weight, and the two above do not. Review replaced
`AdmitsOrder` with `fun _ => True` and both of them still compiled: a theorem saying
portable modes are admitted holds of a predicate that admits everything, so it
cannot detect the drift its docstring claimed to prevent. This one cannot be proved
of a vacuous `AdmitsOrder`, which is what makes `MemoryOrder.IsPortable`
load-bearing rather than merely mentioned.
-/
theorem isPortable_or_registered_of_admitsOrder {vocabulary : AdmittedVocabulary}
    {order : MemoryOrder} (h : vocabulary.AdmitsOrder order) :
    order.IsPortable ∨
      ∃ name, order.profileName? = some name ∧ vocabulary.orderingModes.Recognizes name := by
  unfold AdmitsOrder at h
  cases hp : order.profileName? with
  | none => exact Or.inl (MemoryOrder.profileName?_eq_none_iff_isPortable.mp hp)
  | some name =>
      refine Or.inr ⟨name, rfl, ?_⟩
      rw [hp] at h
      exact h

/-- The same for scopes. -/
theorem isPortable_or_registered_of_admitsScope {vocabulary : AdmittedVocabulary}
    {scope : MemoryScope} (h : vocabulary.AdmitsScope scope) :
    scope.IsPortable ∨
      ∃ name, scope.profileName? = some name ∧ vocabulary.orderingScopes.Recognizes name := by
  unfold AdmitsScope at h
  cases hp : scope.profileName? with
  | none => exact Or.inl (MemoryScope.profileName?_eq_none_iff_isPortable.mp hp)
  | some name =>
      refine Or.inr ⟨name, rfl, ?_⟩
      rw [hp] at h
      exact h

/--
Why an access is not admissible, if it is not.

`Admits` is a conjunction, and a consumer that only learns "false" learns almost
nothing: an unregistered ordering mode, an unregistered scope and an unregistered
initialization rule were indistinguishable at the transition, all three reported as
`Grass.Op.StepRejection.accessNotAdmitted`, and the fixtures pinning them asserted a
constructor any failure satisfies. `Grass/Op/Step.lean` argues the opposite standard
for facets — "a rejection says *which* one is missing rather than only that closure
failed" — and follows it for the three fault checks.
-/
inductive AdmissibilityFailure where
  /-- The vocabulary declares no address space by the name the access gives. -/
  | spaceNotDeclared (space : AddressSpaceId)
  /-- The access is not well formed in the vocabulary's version of that space. -/
  | notWellFormedInSpace (space : AddressSpaceId)
  /-- The provenance's allocation source is not one the profile models. -/
  | sourceNotRecognized (source : AllocationSourceId)
  /-- A provenance step kind is not one the profile models. -/
  | stepKindNotRecognized (kind : ProvenanceStepKind)
  /-- An admitted fault class is not one the profile models. -/
  | faultClassNotRecognized (fault : FaultClassId)
  /-- The ledger effect would drop or fabricate a duty. -/
  | ledgerEffectIllFormed
  /-- An obligation kind the effect creates is not one the profile declares. -/
  | obligationKindNotRecognized (kind : ObligationKindId)
  /-- The ordering mode is profile-specific and unregistered. -/
  | orderNotRegistered (name : Name)
  /-- The ordering scope is profile-specific and unregistered. -/
  | scopeNotRegistered (name : Name)
  /-- The initialization rule the access cites is unregistered. -/
  | initializationRuleNotRegistered (name : Name)
  /-- The effect issues a grant of a kind this profile never declared. -/
  | grantKindNotRecognized (kind : GrantKind)
  /-- The effect claims authority under a protocol this profile never declared. -/
  | protocolNotRecognized (protocol : ObligationProtocolId)
deriving DecidableEq, Repr

/--
Every way this access fails to be admissible, in the order the clauses are stated.

**`Admits` is defined from this list, not beside it.** A reason function written
beside a predicate is two encodings of one condition, which is the defect this layer
keeps finding — `AllocationRecord.initialized` and `AccessIntent.isDevice` were both
that, and a first attempt at this was too. Here the list is the definition and
`Admits` is its emptiness, so a clause can only be added in one place.

This is applicability, in the sense of `docs/MEMORY_MODEL.md` §9. An access naming
an address space, allocation source, provenance step kind, fault class, obligation
kind, ordering mode, scope or initialization rule that was never declared fails
here, before any question of whether it would succeed.
-/
def admissibilityFailures (vocabulary : AdmittedVocabulary) (d : AccessDescriptor) :
    List AdmissibilityFailure :=
  (match vocabulary.addressSpaces.find? d.space with
   | Option.none => [.spaceNotDeclared d.space]
   | some space => if d.WellFormedIn space then [] else [.notWellFormedInSpace d.space]) ++
  (if vocabulary.allocationSources.Recognizes d.provenance.source then []
   else [.sourceNotRecognized d.provenance.source]) ++
  (d.provenance.path.filterMap fun step =>
    if vocabulary.provenanceStepKinds.Recognizes step.kind then Option.none
    else some (.stepKindNotRecognized step.kind)) ++
  (d.admittedFaults.filterMap fun fault =>
    if vocabulary.faultClasses.Recognizes fault then Option.none
    else some (.faultClassNotRecognized fault)) ++
  (if d.ledgerEffect.WellFormed then [] else [.ledgerEffectIllFormed]) ++
  (d.ledgerEffect.createdKinds.filterMap fun id =>
    if vocabulary.obligationKinds.Recognizes id then Option.none
    else some (.obligationKindNotRecognized id)) ++
  (match d.ordering.order.profileName? with
   | some name =>
       if vocabulary.orderingModes.Recognizes name then [] else [.orderNotRegistered name]
   | Option.none => []) ++
  (match d.ordering.scope.profileName? with
   | some name =>
       if vocabulary.orderingScopes.Recognizes name then [] else [.scopeNotRegistered name]
   | Option.none => []) ++
  (match d.initialization.justification? with
   | some justification =>
       if vocabulary.initializationJustifications.Recognizes justification then []
       else [.initializationRuleNotRegistered justification]
   | Option.none => []) ++
  (d.authorityEffect.issuedKinds.filterMap fun kind =>
    if vocabulary.grantKinds.Recognizes kind then Option.none
    else some (.grantKindNotRecognized kind)) ++
  (d.ledgerEffect.claimedProtocols.filterMap fun protocol =>
    if vocabulary.protocols.Recognizes protocol then Option.none
    else some (.protocolNotRecognized protocol))

/--
`vocabulary.Admits d` holds when every open name the access descriptor uses is one
this vocabulary declared: nothing failed.

Stated on the vocabulary rather than on the whole profile so that admissibility can
be checked — by a fixture, a report, or a diagnostic — without fabricating the §10
proof package. Claiming closure in order to ask a question about names would be
exactly backwards.
-/
def Admits (vocabulary : AdmittedVocabulary) (d : AccessDescriptor) : Prop :=
  vocabulary.admissibilityFailures d = []

instance (vocabulary : AdmittedVocabulary) (d : AccessDescriptor) :
    Decidable (vocabulary.Admits d) :=
  inferInstanceAs (Decidable (_ = _))

/-- The first reason this access is not admissible, for a rejection to name. -/
def whyNotAdmitted? (vocabulary : AdmittedVocabulary) (d : AccessDescriptor) :
    Option AdmissibilityFailure :=
  (vocabulary.admissibilityFailures d).head?

/-- **The reason and the predicate cannot disagree**: `admits_iff_whyNotAdmitted?_eq_none`
is that, and it is `Iff` on one list rather than a comparison of two encodings. -/
theorem admits_iff_whyNotAdmitted?_eq_none (vocabulary : AdmittedVocabulary)
    (d : AccessDescriptor) :
    vocabulary.Admits d ↔ vocabulary.whyNotAdmitted? d = Option.none := by
  unfold Admits whyNotAdmitted?
  cases vocabulary.admissibilityFailures d <;> simp

/-- Any recorded failure means the access is not admitted. Every clause theorem
below is this, plus a membership proof. -/
theorem not_admits_of_failure {vocabulary : AdmittedVocabulary} {d : AccessDescriptor}
    {failure : AdmissibilityFailure}
    (h : failure ∈ vocabulary.admissibilityFailures d) : ¬ vocabulary.Admits d := by
  intro ha
  unfold Admits at ha
  rw [ha] at h
  simp at h

/-- A vocabulary declaring no address spaces admits no access. Rejecting
everything is the safe failure; admitting everything would be the permissive
fallback `docs/FOUNDATION.md` law 8 forbids. -/
theorem not_admits_of_no_address_spaces {vocabulary : AdmittedVocabulary}
    (h : vocabulary.addressSpaces = AddressSpaceTable.empty) (d : AccessDescriptor) :
    ¬ vocabulary.Admits d := by
  refine not_admits_of_failure (failure := .spaceNotDeclared d.space) ?_
  unfold admissibilityFailures
  rw [h]
  simp only [List.mem_append]
  refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ?_)))))))))
  simp [AddressSpaceTable.empty, AddressSpaceTable.find?]

/--
A vocabulary never admits an access whose declared space it does not declare, and
never admits one that is not well formed *in that vocabulary's own version* of the
space.

A descriptor names its space and `AddressSpaceTable.find?` resolves it, so the space
its alignment and range checks run against comes from the profile;
`Grass.Op.StepPolicy.vocabularyWellFormed` is the other half.
-/
theorem not_admits_of_undeclared_space {vocabulary : AdmittedVocabulary}
    {d : AccessDescriptor} (h : ¬ vocabulary.addressSpaces.Declares d.space) :
    ¬ vocabulary.Admits d := by
  refine not_admits_of_failure (failure := .spaceNotDeclared d.space) ?_
  unfold admissibilityFailures
  simp only [List.mem_append]
  refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ?_))))))))
  cases hfind : vocabulary.addressSpaces.find? d.space with
  | none => simp
  | some space => exact absurd (by simp [AddressSpaceTable.Declares, hfind]) h

/-- An access naming an unrecognized fault class is not admitted, so a fault the
profile never modelled is not approximated as one it did. -/
theorem not_admits_of_unrecognized_fault {vocabulary : AdmittedVocabulary}
    {d : AccessDescriptor} {fault : FaultClassId} (hmem : fault ∈ d.admittedFaults)
    (h : ¬ vocabulary.faultClasses.Recognizes fault) : ¬ vocabulary.Admits d := by
  refine not_admits_of_failure (failure := .faultClassNotRecognized fault) ?_
  unfold admissibilityFailures
  simp only [List.mem_append, List.mem_filterMap]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨fault, hmem, by simp [h]⟩)))))))

/--
An access whose ledger effect would drop or fabricate a duty is not admitted.

This is what makes `LedgerDelta.WellFormed` a mechanism rather than documentation:
until it was a clause here, `split source []` and `join [] into` were rejected by a
theorem nothing consumed. `docs/OBLIGATIONS.md` §2 and `docs/FOUNDATION.md` law 7.
-/
theorem not_admits_of_ill_formed_ledger_effect {vocabulary : AdmittedVocabulary}
    {d : AccessDescriptor} (h : ¬ d.ledgerEffect.WellFormed) : ¬ vocabulary.Admits d := by
  refine not_admits_of_failure (failure := .ledgerEffectIllFormed) ?_
  unfold admissibilityFailures
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simp [h])))))))

/-- **An access claiming a protocol the profile never declared is not admitted.**

The clause that makes `ProtocolAuthority` mean anything. The type index stops
authority for one protocol being presented for another; nothing stopped it being
minted for any protocol at all, by any module, since `mintedBy` is public and total.
Review minted one from a string in a foreign file and discharged a duty another
family had created. A protocol the profile did not declare is refused here, before
`LedgerEffectApplicable` is asked whether the delta is applicable. -/
theorem not_admits_of_undeclared_protocol {vocabulary : AdmittedVocabulary}
    {d : AccessDescriptor} {protocol : ObligationProtocolId}
    (hmem : protocol ∈ d.ledgerEffect.claimedProtocols)
    (h : ¬ vocabulary.protocols.Recognizes protocol) : ¬ vocabulary.Admits d := by
  refine not_admits_of_failure (failure := .protocolNotRecognized protocol) ?_
  unfold admissibilityFailures
  simp only [List.mem_append, List.mem_filterMap]
  exact Or.inr ⟨protocol, hmem, by simp [h]⟩

/-- **An access issuing a grant of a kind the profile never declared is not
admitted.**

The clause that stops an operation inventing an authority kind. It matters because
`MemoryState.AnyGrantOver` is kind-blind: every rule that asks whether anything is
held over some bytes counts a grant of any kind, so an invented kind freezes bytes
even though no provider's `GrantedOfKind` will ever match it. Before
`AccessDescriptor.authorityEffect` existed only a fixture could mint one, which is
why this registry arrived a milestone after the others. -/
theorem not_admits_of_undeclared_grant_kind {vocabulary : AdmittedVocabulary}
    {d : AccessDescriptor} {kind : GrantKind}
    (hmem : kind ∈ d.authorityEffect.issuedKinds)
    (h : ¬ vocabulary.grantKinds.Recognizes kind) : ¬ vocabulary.Admits d := by
  refine not_admits_of_failure (failure := .grantKindNotRecognized kind) ?_
  unfold admissibilityFailures
  simp only [List.mem_append, List.mem_filterMap]
  exact Or.inl (Or.inr ⟨kind, hmem, by simp [h]⟩)

/-- An access creating an obligation of a kind the profile never declared is not
admitted. -/
theorem not_admits_of_undeclared_obligation_kind {vocabulary : AdmittedVocabulary}
    {d : AccessDescriptor} {kind : ObligationKindId}
    (hmem : kind ∈ d.ledgerEffect.createdKinds)
    (h : ¬ vocabulary.obligationKinds.Recognizes kind) : ¬ vocabulary.Admits d := by
  refine not_admits_of_failure (failure := .obligationKindNotRecognized kind) ?_
  unfold admissibilityFailures
  simp only [List.mem_append, List.mem_filterMap]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨kind, hmem, by simp [h]⟩)))))

/-- **An access citing an initialization rule the profile never declared is not
admitted.** A name no profile claimed is not a rule. This does not rest on
`docs/MEMORY_MODEL.md` §4, which says nothing about uninitialized reads — see
`initializationJustifications`. -/
theorem not_admits_of_unregistered_justification {vocabulary : AdmittedVocabulary}
    {d : AccessDescriptor} {justification : Name}
    (hmem : d.initialization.justification? = some justification)
    (h : ¬ vocabulary.initializationJustifications.Recognizes justification) :
    ¬ vocabulary.Admits d := by
  refine not_admits_of_failure (failure := .initializationRuleNotRegistered justification) ?_
  unfold admissibilityFailures
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr (by rw [hmem]; simp [h])))

/-- **An access requesting an ordering mode the profile never declared is not
admitted.** `docs/MEMORY_MODEL.md` §7.1: an unsupported mapping is rejected. -/
theorem not_admits_of_unregistered_order {vocabulary : AdmittedVocabulary}
    {d : AccessDescriptor} {name : Name}
    (hname : d.ordering.order.profileName? = some name)
    (h : ¬ vocabulary.orderingModes.Recognizes name) : ¬ vocabulary.Admits d := by
  refine not_admits_of_failure (failure := .orderNotRegistered name) ?_
  unfold admissibilityFailures
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by rw [hname]; simp [h])))))

/-- And one claiming a scope the profile never declared is not admitted. A device
fence claiming a scope nobody defined is not a weaker fence; it is an undefined
one. -/
theorem not_admits_of_unregistered_scope {vocabulary : AdmittedVocabulary}
    {d : AccessDescriptor} {name : Name}
    (hname : d.ordering.scope.profileName? = some name)
    (h : ¬ vocabulary.orderingScopes.Recognizes name) : ¬ vocabulary.Admits d := by
  refine not_admits_of_failure (failure := .scopeNotRegistered name) ?_
  unfold admissibilityFailures
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr (by rw [hname]; simp [h]))))

end AdmittedVocabulary

/--
The proof package every memory-capable profile must close.

Exactly the eleven items of `docs/MEMORY_MODEL.md` §10, as fields. They are `Prop`s
supplied by the profile owner, so a `MemoryProfile` value cannot be constructed with
one missing.

**That is weaker than it reads**, and an earlier version of this paragraph called it
"the mechanical content of" §10's gate. All the elaborator asks is that eleven
propositions be *named*, which `RequiredProofPackage`'s own field list is. Nothing relates a field to the profile, to its admitted operations, or
to any theorem in the tree, so a profile supplying `True` eleven times closes §10 and
`Holds` is proved by `trivial`. `Tests/Op/FakeIsa.lean` does exactly that and says
so — but that honesty is the fixture's, not the type's. This is the last gate between
a profile and `VerifiedProgram`, and it is a naming exercise; review found that seven
rounds had asked who consumes this and none had asked whether its content is
constrained. `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 records what closing it would
take.

§10's sentence is "The profile is not usable by `VerifiedProgram` until this package
closes for all of its admitted operations."

Most of these are stated abstractly here and are refined as the milestones that
own them land. That is deliberate: `docs/MEMORY_IMPLEMENTATION_PLAN.md` §3 ships
the list in M1 so an ISA author sees the whole obligation from the first
instruction, and M10 audits that no field was left open.
-/
structure RequiredProofPackage where
  /-- Declared events cover all physical effects. -/
  accessDescriptorSoundness : Prop
  /-- Range, provenance, and initialization are preserved by admitted steps. -/
  rangeProvenanceInitializationPreservation : Prop
  /-- Permissions are enforced and faults are faithful to the hardware model. -/
  permissionEnforcementAndFaultFidelity : Prop
  /-- Loan identities are unique, and split, join, transfer, and reclamation
  obey their laws. -/
  loanMapLaws : Prop
  /-- Every admitted execution has a well-formed consistency graph. -/
  consistencyGraphWellFormedness : Prop
  /-- Verified authority and event combinations imply race freedom. -/
  raceFreedomConsequences : Prop
  /-- Synchronization and obligation transfer obey their laws. -/
  synchronizationAndObligationTransfer : Prop
  /-- Allocators and arenas are fresh, tear down correctly, and invalidate
  epochs. -/
  allocatorFreshnessTeardownEpoch : Prop
  /-- Call-stack and frame lifetimes are preserved. -/
  callStackFrameLifetime : Prop
  /-- Ghost memory and obligation operations survive erasure. -/
  erasurePreservation : Prop
  /-- The profile is connected to its citations and probes. -/
  validationMetadata : Prop

namespace RequiredProofPackage

/--
`package.Holds` is the conjunction of all eleven propositions.

This is what a consumer demands when it wants the §10 package *discharged* rather
than merely enumerated. `VerifiedProgram` will require it; nothing in M1 does,
because the propositions themselves are not yet statable.
-/
def Holds (package : RequiredProofPackage) : Prop :=
  package.accessDescriptorSoundness ∧
  package.rangeProvenanceInitializationPreservation ∧
  package.permissionEnforcementAndFaultFidelity ∧
  package.loanMapLaws ∧
  package.consistencyGraphWellFormedness ∧
  package.raceFreedomConsequences ∧
  package.synchronizationAndObligationTransfer ∧
  package.allocatorFreshnessTeardownEpoch ∧
  package.callStackFrameLifetime ∧
  package.erasurePreservation ∧
  package.validationMetadata

end RequiredProofPackage

/--
A memory profile: what a target admits, and the proofs that make it usable.

`vocabularyVersion` records which version of the foundational vocabulary this
profile was written against. `docs/MEMORY_MODEL.md` §9 versions these
vocabularies and requires extensions to be conservative or to supply migration
theorems, so a profile that does not say which version it assumes cannot be
checked against one.
-/
structure MemoryProfile where
  /-- The profile's nominal identity. -/
  id : Name
  /-- The vocabulary version this profile was written against. -/
  vocabularyVersion : Nat
  /-- The open names this profile admits. -/
  vocabulary : AdmittedVocabulary
  /-- The §10 package. -/
  package : RequiredProofPackage

namespace MemoryProfile

/-!
`MemoryProfile.Admits` used to be here, as `profile.vocabulary.Admits d`, and it is
deleted.

Its docstring said it was "deliberately not decidable", which was false: the body was
a list-emptiness test with a `Decidable` instance three definitions above, and review
wrote the instance in one line and decided a real case with it. It had no call site
either — everything that checks admissibility goes through
`AdmittedVocabulary.whyNotAdmitted?` or `StepPolicy.Admits` — while six docstrings
across four modules named it as the thing that enforces a rule. A dead function with a
false claim about itself, cited as the enforcer, is worse than no function: a reader
auditing "who checks the fault classes" was sent to something that could drift from
whatever actually checks them.

`AdmittedVocabulary.Admits` is the real predicate and it is where the clauses live.
-/

end MemoryProfile

end Grass.Memory
