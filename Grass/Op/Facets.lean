import Grass.Core.Name
import Grass.Memory.Substep

/-!
# Operation facets and the existential operation package

This is the seam an ISA, ABI, or API author implements.

`docs/INSTRUCTIONS.md` §1: "An operation family supplies only the facets it uses,
through separated interfaces rather than one god class... All reachable
operations must close every facet required by their selected profile. Missing
metadata is rejection, not a default empty effect."

## Why this is not in `Memory/`

`MemoryProfile` describes a target's memory policy: what address spaces exist,
what faults are architectural, what the §10 package must discharge. It must not
also hold operation facets, because that would make the memory model depend on a
closed operation universe — every new instruction family would edit `Memory`, and
`Memory` would import ISA definitions, inverting the dependency direction
[MODULES.md](../../docs/MODULES.md) fixes.

The three pieces stay separate:

- `MemoryProfile` is memory policy, and knows nothing about operations;
- `HasOperationFacets Op` is supplied independently by each operation family;
- `SomeOperation` erases the family, so generic stepping consumes facets without
  knowing which ISA produced them.

`Grass/Op/Step.lean` imports Memory and Obligation, consumes facets, and updates
both state machines. Memory does not import operations, and a new ISA family
participates without editing anything below it.

## Why `Op` carries its operands

`substeps : Op → SubstepSequence` takes no environment. An access's address is
computed, so something has to resolve it — but that resolution belongs to the ISA,
whose decode step produces an operation value with its operands already applied.
Threading a family-specific `Env` through this interface would put a type
parameter on every consumer of the seam for a job the family can do itself.
-/

namespace Grass.Op

open Grass.Core Grass.Memory Grass.Obligation

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

/-- Whether an operation may be restarted after an interruption.

`docs/MEMORY_MODEL.md` §7.4 requires restartable or partially executed
instructions to declare their retry discipline. The `OperationFacets` field
existed before this name did, so a profile could not require it — the facet was
declarable and undemandable. -/
def restartability : FacetName := ⟨⟨"restartability"⟩⟩

end FacetName

/--
The facets one operation supplies.

Each is optional at the type level and mandatory at the profile level: see
`Closes`. Absence means "not supplied", never "supplied as empty" — which is the
reading `docs/FOUNDATION.md` law 8 exists to forbid.
-/
structure OperationFacets where
  /-- The accesses this operation performs, if declared. -/
  memoryEffects : Option SubstepSequence := Option.none
  /-- The faults this operation may raise, if declared. -/
  faults : Option (List FaultClassId) := Option.none
  /-- Whether this operation may be restarted, if declared. -/
  restartability : Option Restartability := Option.none
  /-- The ordering this operation requests, if declared. -/
  ordering : Option OrderingDemand := Option.none
deriving DecidableEq, Repr

namespace OperationFacets

/-- Which facets this operation has actually supplied. -/
def supplied (facets : OperationFacets) : List FacetName :=
  (if facets.memoryEffects.isSome then [FacetName.memoryEffects] else []) ++
  (if facets.faults.isSome then [FacetName.faults] else []) ++
  (if facets.ordering.isSome then [FacetName.ordering] else []) ++
  (if facets.restartability.isSome then [FacetName.restartability] else [])

/--
`facets.Closes required` holds when every required facet is supplied.

This is the check `docs/INSTRUCTIONS.md` §1 demands, and
`Grass/Op/Step.lean` refuses to step an operation that fails it.
-/
def Closes (facets : OperationFacets) (required : List FacetName) : Prop :=
  ∀ facet ∈ required, facet ∈ facets.supplied

instance (facets : OperationFacets) (required : List FacetName) :
    Decidable (facets.Closes required) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The accesses this operation performs, treating an undeclared memory-effect
facet as *no answer* rather than as no effect. -/
def substeps? (facets : OperationFacets) : Option SubstepSequence := facets.memoryEffects

/-- An operation supplying nothing closes nothing but the empty requirement.
Silence is not a declaration. -/
@[simp] theorem supplied_default : ({} : OperationFacets).supplied = [] := rfl

theorem not_closes_of_missing {facets : OperationFacets} {required : List FacetName}
    {facet : FacetName} (hr : facet ∈ required) (hs : facet ∉ facets.supplied) :
    ¬ facets.Closes required := fun h => hs (h facet hr)

/--
**Closure is exactly what `Grass/Op/Step.lean`'s first gate decides.**

Two docstrings -- this module's above and `Grass/Memory/Fault.lean`'s -- said `step`
refuses an operation that fails `Closes`, and `step` refuses on a `List.find?` over
the same list, which is not the same sentence. Review pointed out that nothing under
`Grass/` applied `Closes` at all: it was a `def` two modules named as the check, which
is the shape `MemoryProfile.Admits` had before it was deleted, and the shape
`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 records as falling between two audits.

This is the missing step. `step` uses `find?` to *name* the failing facet, and this
says the answer `find?` gives is `Closes`'s answer, so the docstrings above are now
claims about a theorem rather than about a resemblance.
-/
theorem closes_iff_no_missing (facets : OperationFacets) (required : List FacetName) :
    facets.Closes required ↔
      required.find? (fun facet => !facets.supplied.contains facet) = Option.none := by
  constructor
  · intro h
    refine List.find?_eq_none.2 (fun facet hmem => ?_)
    simpa using List.elem_eq_true_of_mem (h facet hmem)
  · intro h facet hmem
    have := List.find?_eq_none.1 h facet hmem
    simpa using this

end OperationFacets

/--
An operation family declares its facets by instance.

Supplied independently by every instruction, API, macro, or device family. There
is no master sum type and no registry to edit: a family introduces its own `Op`
and its own instance, and nothing below it changes.
-/
class HasOperationFacets (Op : Type) where
  /-- The facets of a given operation of this family. -/
  facets : Op → OperationFacets

/--
An operation with its family erased.

`docs/INSTRUCTIONS.md` §1 requires open extensibility "without editing a closed
master sum type". This is that openness: generic stepping takes a
`SomeOperation`, and two independently written families are packaged the same way
without either knowing about the other.

The package carries its own evidence — the family's `HasOperationFacets`
instance — rather than looking one up. `docs/FOUNDATION.md` law 6 forbids ambient
provider choice, and a registry keyed by name would be exactly that, with the
added failure mode of a lookup that can miss.
-/
structure SomeOperation : Type 1 where
  /-- The operation family's type. -/
  Op : Type
  /-- The operation itself. -/
  op : Op
  /-- The family's facet declaration. -/
  instance_ : HasOperationFacets Op

namespace SomeOperation

/-- The facets of the packaged operation. -/
def facets (some : SomeOperation) : OperationFacets := some.instance_.facets some.op

/-- Package an operation whose family has declared its facets. -/
def of {Op : Type} [inst : HasOperationFacets Op] (op : Op) : SomeOperation :=
  { Op := Op, op := op, instance_ := inst }

@[simp] theorem facets_of {Op : Type} [inst : HasOperationFacets Op] (op : Op) :
    (SomeOperation.of op).facets = inst.facets op := rfl

end SomeOperation

end Grass.Op
