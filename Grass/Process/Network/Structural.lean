import Grass.Process.Spec

/-!
# The structural process network

`agent-bus` disposition `coord1:4`, ruling on issue `c-process:3`:

> ratify one canonical structural process-network abstraction, owned by Process
> and containing no `BehaviorContract`, `denotation`, `traceDenotation`, or
> exactness field. Preserve the role-schema/instance/protocol/composition shape
> actually used by the spikes, generalized over its protocol family so Process
> does not import Semantics. Semantics retains precious `SpecProcess` behavior.
> A `ProcessPresentation`/refinement object above both layers connects a chosen
> network trace to `spec.contract` and requirements.

The defect it settles was two incompatible declarations of one name.
`docs/PROCESS.md` §2 declared `AbstractSpecificationProcessNetwork` with
`registry`, `root`, `channels`, `linearState`, `sharedState`, `abstraction`,
`denotation`, `traceDenotation`, `exact`; `docs/SEMANTICS.md` declared a
different structure of the same name with `RoleSchema`, `finiteSchemas`,
`Instance`, `protocol`, `instances`, `composition`. Every consumer used the
second — both spikes and `docs/REFINEMENT.md` — while `REFINEMENT.md` also read
`traceDenotation` from the first.

## What is deliberately absent

No `denotation`, no `traceDenotation`, no `exact`. This structure says which
roles exist, how many instances each has, and which protocol each speaks. It
says nothing about what the network *means*, and it cannot: a `BehaviorContract`
is `docs/SEMANTICS.md`'s, and a network that carried one would put Process above
Semantics and re-create the cycle `coord1:5` just cut.

`Tests/Process/StructuralNetworkFixtures.lean` pins that absence with an
elaboration fixture, so neither historical field family can return silently.

## Generalized over the protocol family

`Protocol` and `InstanceOf` are parameters. `Grass.Semantics` instantiates them
at `SpecProcess resources` and its protocol instances; a plan built entirely
inside Process instantiates them at `ProcessSpec` and its requests. That
parameter is exactly what lets this module sit below Semantics while the shape
the spikes write stays the same.

`docs/FOUNDATION.md` law 15 applies to the whole of it: a role decomposition is
a reviewed replaceable construction input, never precious program meaning.
-/

namespace Grass.Process

universe u w v r

/--
Which roles a realization has, how many of each, and what protocol each speaks.

The shape `docs/SEMANTICS.md` declared and both spikes instantiate, with the
protocol family abstracted so this can sit below the layer that owns behavior.
-/
structure StructuralProcessNetwork (Protocol : Type v)
    (InstanceOf : Protocol → Type r) where
  /-- The roles. -/
  RoleSchema : Type r
  /--
  Every role, listed.

  `docs/SEMANTICS.md` wrote `finiteSchemas : Fintype RoleSchema`. Lean core has
  no `Fintype`, and this is what that class supplies for the uses here: a list
  to fold over and a guarantee it is complete. It stays elementary rather than
  pulling in a dependency for one field.
  -/
  schemas : List RoleSchema
  /-- The list omits no role. -/
  schemasComplete : ∀ schema, schema ∈ schemas
  /-- And repeats none, so a fold over it counts each role once. -/
  schemasDistinct : schemas.Nodup
  /-- Which protocol each role speaks. -/
  protocol : RoleSchema → Protocol
  /-- The identities of that role's instances. -/
  Instance : RoleSchema → Type r
  /-- Each instance is an instance of its role's protocol. -/
  instanceOf : ∀ schema, Instance schema → InstanceOf (protocol schema)

namespace StructuralProcessNetwork

variable {Protocol : Type v} {InstanceOf : Protocol → Type r}
  (network : StructuralProcessNetwork Protocol InstanceOf)

/-- The number of roles. Finite, by `schemas`. -/
def roleCount : Nat := network.schemas.length

/--
A role is reachable in the listing, so any property proved by folding `schemas`
holds of every role.

This is what `schemasComplete` is for, and the form an aggregate check consumes:
`docs/PROCESS_SHARDING.md` §6's namespace-uniqueness and root-reachability folds
are folds over exactly this list.
-/
theorem forall_roles {motive : network.RoleSchema → Prop}
    (onListed : ∀ schema ∈ network.schemas, motive schema)
    (schema : network.RoleSchema) : motive schema :=
  onListed schema (network.schemasComplete schema)

/--
The population is nonempty at every role: each role has at least one instance.

**A composition law is a `Prop`, and this is one.** An earlier revision wrapped
laws in `structure CompositionLaw where holds : Prop` — one field, none of them
a proof — on the reasoning that "a network with no law attached is honestly a
network with no law attached". That reasoning is sound and the wrapper did not
serve it: a network *with* a `CompositionLaw` was also a network with no law
attached, because `⟨False⟩` inhabits it and nothing anywhere required `holds`.
An emptiness sweep found the structure constructed nowhere in the corpus, which
is what a contentless record looks like from the outside.
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.84.

`docs/SEMANTICS.md` had `composition : AbstractNetworkCompositionLaw protocol
instances` as a *field* of the network, and splitting it out remains right: a
caller states the laws their realization actually needs. They state them as
propositions.

This is the commonest such law, provided because a realization that needs it
should not have to spell it. A role with no instances is usually a modelling
error — it is a protocol nothing speaks — though it is legitimate for a role that
only appears under a resource policy, which is why this is a law rather than a
field.
-/
def EveryRolePopulated : Prop :=
  ∀ schema : network.RoleSchema, Nonempty (network.Instance schema)

end StructuralProcessNetwork

end Grass.Process
