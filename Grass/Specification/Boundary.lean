import Grass.Specification.Scope

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

## Why it is in the neutral layer

`agent-bus` disposition `coord1:5`, ruling on issue `c-process:4`:

> ratify an acyclic diamond. Move pure DriverBoundary/common demand-result
> vocabulary into the neutral Specification layer below both Semantics and
> Process. Semantics owns SpecProcess and BehaviorContract; Process owns
> replaceable structural networks and execution machinery; Refinement/Weave owns
> ProcessPresentation and theorems relating network traces to a SpecProcess.
> Neither Semantics nor Process may import the other merely to state its core
> objects.

The cycle that ruling resolves was real: `docs/SEMANTICS.md` states
`SpecProcess.driverBoundary` in terms of this record, while
`docs/PROCESS.md`'s abstract network carried a `BehaviorContract`, which
`Grass.Semantics` owns. `docs/MODULES.md` declares a strict chain, so neither
layer could be written first.

An earlier version of this module lived at `Grass/Process/Network/Boundary.lean`
and imported `Grass.Process.Spec` in order to offer a `toVocabulary` view. That
edge is what made the placement wrong rather than merely unconventional: a
neutral record cannot depend on the layer that consumes it. The view moved to
`Grass/Process/Network/Exposure.lean`, which is Process-side and is allowed to
know both.

This module therefore imports exactly one thing: the scope identity its
requirement keys are named in.
-/

namespace Grass.Specification

universe u

/--
A nominal requirement key: what a realization demands of its platform.

`docs/FOUNDATION.md` law 6 forbids ambient provider choice, and law 14 requires
that changing one requirement invalidate only what depends on it. Both need
requirements to be *named*, scoped, and comparable, which is why this is a scope
plus a name and not a proposition.
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

end DriverBoundary

end Grass.Specification
