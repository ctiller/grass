import Grass.Process.Scope
import Grass.Process.Spec

/-!
# The driver boundary

`docs/PROCESS.md` §2 declares `DriverBoundary` as the stable interface between a
process realization and everything below it:

```text
structure DriverBoundary where
  ExternalEvent : Type
  Demand : Type
  Result : Demand -> Type
  Observation : Type
  requirements : RequirementSet
```

§4 says what that stability is worth:

> A program can move from synthesized degeneracy to an explicit plan without
> changing `spec` or the stable assembly `DriverBoundary`; a progress bar,
> Ctrl+C handler, or worker thread therefore extends the same proof algebra
> rather than forcing a rewrite.

So this record is deliberately poor. It has no topology, no root, no plan, no
population, and no channel. Anything added to it becomes a fact that assembly
and platform proofs depend on, and every one of those is a fact a plan change
would then be able to break.

## Imports

This module imports `Grass.Process.Scope` for the requirement key's scope and
`Grass.Process.Spec` for the vocabulary view. It deliberately does *not* import
the protocol registry: a boundary has nothing to do with keys, and importing the
registry to reach one path type would put every registry change in the rebuild
cone of every requirement change, which `docs/OLEAN_SHARDING.md` §2 names as a
forbidden edge.

## Why this module sits below `Grass.Semantics`

`docs/SEMANTICS.md` defines `SpecProcess.driverBoundary` and therefore imports
this type, while `docs/MODULES.md` puts `Process` above `Semantics`. That is a
cycle, and `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.2 proposes the cut taken
here: `DriverBoundary` carries no semantic content — no contract, no oracle, no
resource model — so it can and does sit below the semantics layer, and only the
*projection* from a plan's root demands to this boundary needs anything above.

That projection is M2 work. This module is the boundary alone.
-/

namespace Grass.Process

universe u v

/--
A nominal requirement key: what a realization demands of its platform.

`docs/FOUNDATION.md` law 6 forbids ambient provider choice, and law 14 requires
that changing one requirement invalidate only what depends on it. Both need
requirements to be *named*, scoped, and comparable, which is why this is a
scope plus a name and not a proposition.
-/
structure RequirementKey where
  /-- The scope that owns this requirement. -/
  scope : ScopeId
  /-- The requirement's name within that scope. -/
  name : String
  deriving DecidableEq, Repr

/--
The requirements a boundary carries.

Duplicate-free: a requirement demanded twice is demanded once, and a set that
recorded it twice would make the coverage fold at closure count wrong.
-/
structure RequirementSet where
  /-- The demanded keys. -/
  keys : List RequirementKey
  /-- Each key appears once. -/
  distinct : keys.Nodup

namespace RequirementSet

/-- The empty requirement set. -/
def empty : RequirementSet where
  keys := []
  distinct := List.nodup_nil

/-- `key` is demanded by this set. -/
def Demands (requirements : RequirementSet) (key : RequirementKey) : Prop :=
  key ∈ requirements.keys

/--
One set demands everything another does.

This is the direction a refinement delta accumulates: `docs/PROCESS.md` §8 says
"Requirement deltas accumulate in the explicit `ProviderEnv`", and a lowering
step may add requirements but may not silently drop one.
-/
def Covers (larger smaller : RequirementSet) : Prop :=
  ∀ key, smaller.Demands key → larger.Demands key

theorem Covers.refl (requirements : RequirementSet) :
    requirements.Covers requirements := fun _ demanded => demanded

theorem Covers.trans {a b c : RequirementSet}
    (outer : a.Covers b) (inner : b.Covers c) : a.Covers c :=
  fun key demanded => outer key (inner key demanded)

@[simp] theorem not_empty_demands (key : RequirementKey) :
    ¬ empty.Demands key := List.not_mem_nil

end RequirementSet

/--
The interface a driver realizes: what enters, what is asked for, what answers
are permitted, what is observed, and what the platform must supply.

Deliberately poor; see the module note.
-/
structure DriverBoundary : Type (u + 1) where
  /-- Entropy the driver delivers into the process network. -/
  ExternalEvent : Type u
  /-- The interactions the network exports to the driver. -/
  Demand : Type u
  /-- The permitted answers to each exported demand. -/
  Result : Demand → Type u
  /-- What a commit may append to the observed trace. -/
  Observation : Type u
  /-- What the platform must supply for this boundary to be realizable. -/
  requirements : RequirementSet

namespace DriverBoundary

/--
The vocabulary of a process that exposes exactly this boundary.

The fault, interruption, and violation classes are `PEmpty` because they are not
boundary concepts: a driver delivers entropy, results, and nothing else, and a
process's own fault classification is private to it. A realization that needs to
surface a provider failure does so as a `Result` value of the demand that
failed, which is what makes it a dependent, exhaustively-handled outcome rather
than an out-of-band channel.
-/
def toVocabulary (boundary : DriverBoundary.{u}) : ProcessVocabulary.{u} where
  ExternalEvent := boundary.ExternalEvent
  Demand := boundary.Demand
  Result := boundary.Result
  Observation := boundary.Observation
  InterruptReason := PEmpty
  LogicalFault := PEmpty
  EnvironmentViolation := PEmpty

@[simp] theorem toVocabulary_ExternalEvent (boundary : DriverBoundary.{u}) :
    boundary.toVocabulary.ExternalEvent = boundary.ExternalEvent := rfl

@[simp] theorem toVocabulary_Demand (boundary : DriverBoundary.{u}) :
    boundary.toVocabulary.Demand = boundary.Demand := rfl

@[simp] theorem toVocabulary_Observation (boundary : DriverBoundary.{u}) :
    boundary.toVocabulary.Observation = boundary.Observation := rfl

@[simp] theorem toVocabulary_Result (boundary : DriverBoundary.{u}) :
    boundary.toVocabulary.Result = boundary.Result := rfl

/--
Replace a boundary's requirement set, leaving its interface alone.

Replacement, not strengthening: an earlier docstring claimed the result
"provably covers the original", which is false — passing `RequirementSet.empty`
drops everything. Use `demandAlso` for the monotone operation.
-/
def withRequirements (boundary : DriverBoundary.{u})
    (requirements : RequirementSet) : DriverBoundary.{u} :=
  { boundary with requirements := requirements }

@[simp] theorem withRequirements_requirements (boundary : DriverBoundary.{u})
    (requirements : RequirementSet) :
    (boundary.withRequirements requirements).requirements = requirements := rfl

/--
Demand one more thing of the platform.

`docs/PROCESS.md` §8: a local refinement "introduces a finite requirement
delta", and deltas accumulate rather than replace — a lowering step may add
requirements but may not silently drop one. `demandAlso_covers` is that
guarantee, so a proof stated against the weaker boundary still applies.
-/
def demandAlso (boundary : DriverBoundary.{u}) (key : RequirementKey) :
    DriverBoundary.{u} :=
  if present : key ∈ boundary.requirements.keys then
    boundary
  else
    boundary.withRequirements
      ⟨key :: boundary.requirements.keys,
        List.nodup_cons.mpr ⟨present, boundary.requirements.distinct⟩⟩

theorem demandAlso_covers (boundary : DriverBoundary.{u}) (key : RequirementKey) :
    (boundary.demandAlso key).requirements.Covers boundary.requirements := by
  intro demanded member
  unfold demandAlso
  split
  · exact member
  · exact List.mem_cons_of_mem key member

theorem demandAlso_demands (boundary : DriverBoundary.{u}) (key : RequirementKey) :
    (boundary.demandAlso key).requirements.Demands key := by
  unfold demandAlso
  split
  · assumption
  · exact List.mem_cons_self

/-!
`toVocabulary` and the requirement-delta operations above have no consumer inside
`Grass.Process` yet. `toVocabulary` is what the sequential adapter elaborates a
`SequentialMachine` into, and `demandAlso` with `RequirementSet.Covers` is the
delta a refinement lens accumulates; both are M4. They are declared here, with
the boundary they are about, rather than invented at the use site.
-/

end DriverBoundary

end Grass.Process
