import Grass.Core.Name
import Grass.Memory.Event
import Grass.Memory.Substep

/-!
# Operation facets

This is the seam an ISA, ABI, or API author implements.

`docs/INSTRUCTIONS.md` §1: "An operation family supplies only the facets it uses,
through separated interfaces rather than one god class... All reachable
operations must close every facet required by their selected profile. Missing
metadata is rejection, not a default empty effect."

## Structures, not classes

A facet is an explicit value held by a profile, not a typeclass resolved by
instance search. `docs/DECISIONS.md` rejects "choosing providers through ambient
global instance search" outright, and `docs/FOUNDATION.md` law 6 forbids ambient
provider choice. An instance-resolved facet would also make "which facet did this
operation actually use" a question about the elaborator's search order rather
than about the profile, which is the opposite of what the §10 audit needs.

## Effects depend on operands

`substeps` takes an environment as well as an operation, because an access's
address is computed. `lea rax, [rip + payload]` and `mov rax, [rip + payload]`
differ in whether they access at all; `mov rax, [rbx]` cannot say what it touches
without knowing `rbx`. `Env` is the ISA's own operand and machine environment,
which keeps this module below the ISA rather than above it.

## Closure is checked, not assumed

`OperationFacets` holds each facet as an `Option`, and `Closes` demands that every
facet a profile requires is present. An operation family that has not supplied
its memory effects fails that check. It does not default to "no memory effect",
which is the reading law 8 exists to forbid.
-/

namespace Grass.Memory

open Grass.Core

/-- The name of an operation facet. -/
structure FacetName where
  /-- The facet's nominal name. -/
  name : Name
deriving DecidableEq, Repr

namespace FacetName

/-- The memory accesses an operation performs. -/
def memoryEffects : FacetName := ⟨⟨"memoryEffects"⟩⟩

/-- The architectural faults an operation may raise. -/
def faults : FacetName := ⟨⟨"faults"⟩⟩

/-- The atomicity and ordering an operation requests. -/
def ordering : FacetName := ⟨⟨"ordering"⟩⟩

/-- The obligations an operation creates, discharges, or transfers. -/
def obligations : FacetName := ⟨⟨"obligations"⟩⟩

/-- The observations an operation emits. -/
def observations : FacetName := ⟨⟨"observations"⟩⟩

end FacetName

/--
The memory-effect facet: what accesses an operation performs.

`wellFormed` is a field rather than a separate obligation, so a facet cannot be
constructed for an operation whose declared accesses are internally inconsistent.
The check is intrinsic; whether those accesses are *permitted* against a state is
M2's `applyAccess`.
-/
structure MemoryEffectFacet (Op : Type) (Env : Type) where
  /-- The accesses `op` performs in environment `env`. -/
  substeps : Op → Env → SubstepSequence
  /-- Every declared access is intrinsically well formed. -/
  wellFormed : ∀ op env, (substeps op env).WellFormed

/--
The fault facet: which architectural faults an operation may raise, and whether
it may be restarted.

`docs/MEMORY_MODEL.md` §7.4 requires restartability to be declared rather than
assumed, so it is a total function here with no default.
-/
structure FaultFacet (Op : Type) where
  /-- The faults `op` may raise. A fault outside this list is a model
  discrepancy, and per `docs/FOUNDATION.md` law 10 becomes a validation finding. -/
  admitted : Op → List FaultClassId
  /-- Whether `op` may be re-executed after an interruption. -/
  restartability : Op → Restartability

/--
The ordering facet: the atomicity and ordering an operation requests.

Separate from the memory-effect facet because a fence requests ordering while
accessing nothing, and an operation may be atomic without this module knowing its
accesses.
-/
structure OrderingFacet (Op : Type) where
  /-- The ordering `op` requests. -/
  demand : Op → OrderingDemand

/--
The facets an operation family supplies.

Each is optional at the type level and mandatory at the profile level: see
`Closes`. Absence means "not supplied", never "supplied as empty".
-/
structure OperationFacets (Op : Type) (Env : Type) where
  /-- The memory accesses this family performs, if declared. -/
  memoryEffects : Option (MemoryEffectFacet Op Env) := Option.none
  /-- The faults this family may raise, if declared. -/
  faults : Option (FaultFacet Op) := Option.none
  /-- The ordering this family requests, if declared. -/
  ordering : Option (OrderingFacet Op) := Option.none

namespace OperationFacets

variable {Op Env : Type}

/-- Which facets this family has actually supplied. -/
def supplied (facets : OperationFacets Op Env) : List FacetName :=
  (if facets.memoryEffects.isSome then [FacetName.memoryEffects] else []) ++
  (if facets.faults.isSome then [FacetName.faults] else []) ++
  (if facets.ordering.isSome then [FacetName.ordering] else [])

/--
`facets.Closes required` holds when every required facet is supplied.

This is the check `docs/INSTRUCTIONS.md` §1 demands. A family failing it is
rejected; there is no path by which the missing facet becomes an empty effect.
-/
def Closes (facets : OperationFacets Op Env) (required : List FacetName) : Prop :=
  ∀ facet ∈ required, facet ∈ facets.supplied

instance (facets : OperationFacets Op Env) (required : List FacetName) :
    Decidable (facets.Closes required) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- A family supplying nothing closes nothing but the empty requirement. This is
the statement that silence is not a declaration. -/
@[simp] theorem supplied_default : (({} : OperationFacets Op Env)).supplied = [] := rfl

theorem not_closes_of_missing {facets : OperationFacets Op Env} {required : List FacetName}
    {facet : FacetName} (hr : facet ∈ required) (hs : facet ∉ facets.supplied) :
    ¬ facets.Closes required := fun h => hs (h facet hr)

end OperationFacets

end Grass.Memory
