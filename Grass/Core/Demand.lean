import Grass.Core.Identifiers

/-!
# Independently keyed theorem demands

The family is open in its key type and carries an exact nominal kind as
metadata. Finiteness is exposed as an explicit, duplicate-free enumeration so
diagnostics and future build manifests need not recover it from an
implementation-specific map.
-/

namespace Grass

universe u

/--
Exact invalidation and diagnostic metadata for theorem demands.

`extension owner kind` is an identity, not a semantic fallback. A future
semantic consumer must resolve extension identities through a typed registry
and reject unknown identities rather than assign default meaning.
This is the contract ratified by agent-bus ruling `g-design:13`.
-/
inductive RequirementKind where
  | functional
  | safety
  | memory
  | concurrency
  | progress
  | termination
  | resource
  | obligation
  | diagnostic
  | applicability
  | artifact
  | extension (owner kind : StableId)
deriving Repr, DecidableEq

namespace RequirementKind

/-- `RequirementKind.extension_injective` proves nominal pairs cannot collapse. -/
theorem extension_injective {ownerA kindA ownerB kindB : StableId} :
    extension ownerA kindA = extension ownerB kindB ↔
      ownerA = ownerB ∧ kindA = kindB := by
  simp

end RequirementKind

/-- A finite family of propositions which must be certified independently. -/
structure DemandFamily where
  Key : Type u
  keys : List Key
  complete : forall key, key ∈ keys
  unique : keys.Nodup
  identity : Key -> RequirementKey
  identityInjective : Function.Injective identity
  /-- Exact metadata only; semantic use requires typed, reject-unknown resolution. -/
  kind : Key -> RequirementKind
  statement : Key -> Prop

/-- Evidence for every member of one exact demand family. -/
structure DemandCertificateFamily (demands : DemandFamily.{u}) : Prop where
  discharge : forall key, demands.statement key

/-- Stable identities exported by one exact finite family. -/
def DemandFamily.identities (demands : DemandFamily) : List RequirementKey :=
  demands.keys.map demands.identity

namespace DemandFamily

/-- Every demand's stable identity occurs in the exported identity list. -/
@[simp]
theorem identity_mem_identities (demands : DemandFamily) (key : demands.Key) :
    demands.identity key ∈ demands.identities := by
  exact List.mem_map.mpr ⟨key, demands.complete key, rfl⟩

/-- The exported stable identity enumeration contains no duplicates. -/
theorem identities_nodup (demands : DemandFamily) : demands.identities.Nodup :=
  demands.unique.map demands.identity fun _ _ distinct equal =>
    distinct (demands.identityInjective equal)

end DemandFamily

/-- Auditable origin of a later-stage demand. -/
inductive RequirementOrigin (priorKeys : List RequirementKey) where
  | prior (key : RequirementKey) (present : key ∈ priorKeys)
  | external (authority : StableId)

/-- A later-stage family fresh from every cumulative prior stable key. -/
structure DerivedDemandFamily (priorKeys : List RequirementKey) where
  demands : DemandFamily.{u}
  origin : demands.Key -> RequirementOrigin priorKeys
  fresh : forall derived, demands.identity derived ∉ priorKeys

/-- Cumulative stable keys passed to the next certificate tier. -/
def DerivedDemandFamily.allKeys {priorKeys : List RequirementKey}
    (stage : DerivedDemandFamily priorKeys) : List RequirementKey :=
  priorKeys ++ stage.demands.identities

namespace DerivedDemandFamily

variable {priorKeys : List RequirementKey}

/-- Every prior identity remains visible in the cumulative key list. -/
theorem prior_mem_allKeys (stage : DerivedDemandFamily priorKeys)
    {key : RequirementKey} (present : key ∈ priorKeys) : key ∈ stage.allKeys := by
  exact List.mem_append.mpr (.inl present)

/-- Every newly derived identity is visible in the cumulative key list. -/
@[simp]
theorem identity_mem_allKeys (stage : DerivedDemandFamily priorKeys)
    (key : stage.demands.Key) :
    stage.demands.identity key ∈ stage.allKeys := by
  exact List.mem_append.mpr (.inr (stage.demands.identity_mem_identities key))

/-- `DerivedDemandFamily.allKeys_nodup` states that appending one derived demand
stage preserves uniqueness of cumulative stable identities whenever the prior
enumeration was already unique. -/
theorem allKeys_nodup (stage : DerivedDemandFamily priorKeys)
    (priorUnique : priorKeys.Nodup) : stage.allKeys.Nodup := by
  rw [DerivedDemandFamily.allKeys, List.nodup_append]
  refine ⟨priorUnique, stage.demands.identities_nodup, ?_⟩
  intro prior priorPresent derivedIdentity derivedPresent equal
  rcases List.mem_map.mp derivedPresent with ⟨derived, _, rfl⟩
  exact stage.fresh derived (equal ▸ priorPresent)

end DerivedDemandFamily

namespace DemandCertificateFamily

variable {demands : DemandFamily}

/-- Project the certificate for a single stable key. -/
theorem get (certificates : DemandCertificateFamily demands)
    (key : demands.Key) : demands.statement key :=
  certificates.discharge key

end DemandCertificateFamily

end Grass
