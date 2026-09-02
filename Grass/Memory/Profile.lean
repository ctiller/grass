import Grass.Memory.Audit
import Grass.Memory.Facet
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

## The required proof package

`RequiredProofPackage` is the §10 list, as a record, shipped in M1 even though no
profile closes it until M10. An ISA author writing their first instruction can
then see the whole eventual obligation, and closure becomes a field-by-field
target rather than a discovery. Its fields are `Prop`s the profile owner must
supply; a profile value cannot be built with one missing.
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

The point of the type is that it cannot be constructed without the evidence. A
consumer holding a `Recognized r` is holding a name the profile really listed,
and no `Recognized` exists for a name it did not.
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

Every registry must be listed. A profile with an empty registry on some axis
admits nothing on that axis, which is the safe direction: it rejects rather than
accepting silently.
-/
structure AdmittedVocabulary where
  /-- Address spaces this profile models. -/
  addressSpaces : NameRegistry AddressSpaceId
  /-- Memory types this profile models. -/
  memoryTypes : NameRegistry MemoryTypeId
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
deriving Repr

namespace AdmittedVocabulary

/--
`vocabulary.Admits d` holds when every open name the access descriptor uses is
one this vocabulary declared.

This is applicability, in the sense of `docs/MEMORY_MODEL.md` §9. An access naming
an address space, allocation source, provenance step kind, or fault class that was
never declared is rejected here, before any question of whether it would succeed.

It is stated on the vocabulary rather than on the whole profile so that
admissibility can be checked — by a fixture, a report, or a diagnostic — without
fabricating the §10 proof package. Claiming closure in order to ask a question
about names would be exactly backwards.
-/
def Admits (vocabulary : AdmittedVocabulary) (d : AccessDescriptor) : Prop :=
  vocabulary.addressSpaces.Recognizes d.space.id ∧
  vocabulary.memoryTypes.Recognizes d.space.memoryType ∧
  vocabulary.allocationSources.Recognizes d.provenance.source ∧
  (∀ step ∈ d.provenance.path, vocabulary.provenanceStepKinds.Recognizes step.kind) ∧
  (∀ fault ∈ d.admittedFaults, vocabulary.faultClasses.Recognizes fault)

instance (vocabulary : AdmittedVocabulary) (d : AccessDescriptor) :
    Decidable (vocabulary.Admits d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A vocabulary declaring no address spaces admits no access. Rejecting
everything is the safe failure; admitting everything would be the permissive
fallback `docs/FOUNDATION.md` law 8 forbids. -/
theorem not_admits_of_no_address_spaces {vocabulary : AdmittedVocabulary}
    (h : vocabulary.addressSpaces = NameRegistry.empty) (d : AccessDescriptor) :
    ¬ vocabulary.Admits d := by
  intro ha
  have := ha.1
  rw [h] at this
  exact NameRegistry.not_recognizes_empty d.space.id this

/-- An access naming an unrecognized fault class is not admitted. A fault the
profile never modelled cannot be approximated as one it did. -/
theorem not_admits_of_unrecognized_fault {vocabulary : AdmittedVocabulary}
    {d : AccessDescriptor} {fault : FaultClassId} (hmem : fault ∈ d.admittedFaults)
    (h : ¬ vocabulary.faultClasses.Recognizes fault) : ¬ vocabulary.Admits d :=
  fun ha => h (ha.2.2.2.2 fault hmem)

end AdmittedVocabulary

/--
The proof package every memory-capable profile must close.

Exactly the eleven items of `docs/MEMORY_MODEL.md` §10, as fields. They are
`Prop`s supplied by the profile owner, so a `MemoryProfile` value cannot be
constructed with one missing — which is the mechanical content of "The profile is
not usable by `VerifiedProgram` until this package closes for all of its admitted
operations."

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
  /-- The facets every reachable operation of this profile must supply. -/
  requiredFacets : List FacetName
  /-- The §10 package. -/
  package : RequiredProofPackage

namespace MemoryProfile

/-- `profile.Admits d` holds when the profile's vocabulary recognizes everything
the access descriptor names. -/
def Admits (profile : MemoryProfile) (d : AccessDescriptor) : Prop :=
  profile.vocabulary.Admits d

instance (profile : MemoryProfile) (d : AccessDescriptor) : Decidable (profile.Admits d) :=
  inferInstanceAs (Decidable (profile.vocabulary.Admits d))

end MemoryProfile

end Grass.Memory
