import Grass.Process.Network.Structural
import Tests.Process.M1Fixtures

/-!
# The historical field families cannot return

The fixture `agent-bus` disposition `coord1:4` requires:

> add an elaborating fixture that prevents either historical field family from
> silently returning.

`AbstractSpecificationProcessNetwork` was declared twice. One declaration
carried `registry`, `root`, `channels`, `linearState`, `sharedState`,
`abstraction`, `denotation`, `traceDenotation`, `exact`; the other carried
`RoleSchema`, `finiteSchemas`, `Instance`, `protocol`, `instances`,
`composition`. The ruling keeps the second shape and forbids the semantic
fields of the first.

"Prevents from silently returning" is the operative word. A comment saying
`denotation` is absent would not prevent anything; a `#guard_msgs` on the
elaboration error does, because reintroducing the field makes this file fail.

The positive half is `serverNetwork`: the role-schema shape both spikes actually
write, built over `ProcessSpec` rather than `SpecProcess`, which is what the
protocol-family generalization buys.
-/

namespace Grass.Process.Tests.StructuralNetwork

open Grass.Process

/-! ## The shape the spikes write, over a Process-owned protocol family -/

/-- Roles, as `Spikes/4_Web_Server/Process.lean` declares them. -/
inductive ServerRole
  | listener
  | connection
  | stream
  deriving DecidableEq, Repr

/-- Instance identities per role, as the spike declares them. -/
def ServerRole.Instance : ServerRole → Type
  | .listener => Unit
  | .connection => Nat
  | .stream => Nat × Nat

/--
An instance of a protocol is a request to it.

`InstanceOf` is a parameter of the network, so this is the Process-side choice.
`Grass.Semantics` will instantiate it differently, at its own protocol
instances, over the *same* structure.
-/
@[reducible] def requestOf (protocol : ProcessSpec.{0, 0}) : Type := protocol.Request

/--
The network. Note what it does not contain: no denotation, no trace denotation,
no exactness field, and no `BehaviorContract` anywhere.

All three roles speak `countdown` here, which is deliberate — role identity is
`RoleSchema`, not the protocol a role maps to, and a listener and a worker may
perfectly well share a standard protocol.
-/
def serverNetwork : StructuralProcessNetwork ProcessSpec.{0, 0} requestOf where
  RoleSchema := ServerRole
  schemas := [.listener, .connection, .stream]
  schemasComplete := by intro schema; cases schema <;> simp
  schemasDistinct := by decide
  protocol := fun _ => countdown
  Instance := ServerRole.Instance
  instanceOf := fun schema _ =>
    match schema with
    | .listener => 0
    | .connection => 0
    | .stream => 0

theorem serverNetwork_has_three_roles : serverNetwork.roleCount = 3 := rfl

/-- Every role is covered by the listing, so a fold over `schemas` is total. -/
theorem every_role_listed (schema : ServerRole) :
    schema ∈ serverNetwork.schemas := serverNetwork.schemasComplete schema

/--
Distinct roles sharing a protocol are still distinct.

The fact the module note claims and this network exhibits: `listener` and
`stream` map to the same protocol and are not the same role.
-/
theorem shared_protocol_distinct_roles :
    serverNetwork.protocol .listener = serverNetwork.protocol .stream ∧
      (ServerRole.listener ≠ ServerRole.stream) := by
  refine ⟨rfl, ?_⟩
  decide

/-! ## A wrapper keeps the short author spelling

`docs/SEMANTICS.md`'s `ProcessPresentationNetwork` wraps a structural network in
a field called `roles` and adds a composition law. `g-design:28` observed that
its consumers — `docs/REFINEMENT.md` and Spike 5 — write `network.RoleSchema`
and `network.protocol schema`, which a bare wrapper does not provide, and that
making every consumer spell `network.roles.protocol` would leak the wrapper's
representation and add permanent ceremony.

The fix is forwarding accessors, now declared in `SEMANTICS.md`. That structure
has no Lean layer yet, so what is pinned here is the *pattern*, on the structure
this layer does own: a wrapper with forwarding abbreviations is transparent, and
the short spelling means exactly the long one. When `Grass.Semantics` lands, its
own fixture replaces this one.
-/

/-- A wrapper shaped like `ProcessPresentationNetwork`. -/
structure WrappedNetwork where
  roles : StructuralProcessNetwork ProcessSpec.{0, 0} requestOf

namespace WrappedNetwork

abbrev RoleSchema (network : WrappedNetwork) : Type := network.roles.RoleSchema

abbrev protocol (network : WrappedNetwork) :
    network.RoleSchema → ProcessSpec.{0, 0} := network.roles.protocol

abbrev Instance (network : WrappedNetwork) : network.RoleSchema → Type :=
  network.roles.Instance

abbrev schemas (network : WrappedNetwork) : List network.RoleSchema :=
  network.roles.schemas

end WrappedNetwork

/-- The wrapped server. -/
def wrappedServer : WrappedNetwork := ⟨serverNetwork⟩

/-- The short spelling elaborates, which is the whole point of the accessors. -/
theorem wrapper_role_schema_usable (schema : wrappedServer.RoleSchema) :
    schema ∈ wrappedServer.schemas := serverNetwork.schemasComplete schema

/-- And it means exactly the long spelling; the wrapper is transparent. -/
theorem wrapper_protocol_agrees (schema : wrappedServer.RoleSchema) :
    wrappedServer.protocol schema = wrappedServer.roles.protocol schema := rfl

/--
A consumer written against the short spelling type-checks.

This is the shape `docs/REFINEMENT.md` uses for `resourceView`, and the reason
`g-design:28` asked for the accessors rather than accepting `network.roles.*`
at every use site.
-/
def rolePredicate (network : WrappedNetwork) : Type :=
  network.RoleSchema → Prop

theorem rolePredicate_is_over_roles :
    rolePredicate wrappedServer = (ServerRole → Prop) := rfl

/-! ## Neither historical field family can return

Each case names a field from one of the two old declarations. If anyone adds it
back to `StructuralProcessNetwork`, the corresponding `#guard_msgs` stops
matching and this file fails to build.
-/

/--
error: Invalid field `denotation`: The environment does not contain `Grass.Process.StructuralProcessNetwork.denotation`, so it is not possible to project the field `denotation` from an expression
  serverNetwork
of type
  StructuralProcessNetwork ProcessSpec requestOf
-/
#guard_msgs in
example := serverNetwork.denotation

/--
error: Invalid field `traceDenotation`: The environment does not contain `Grass.Process.StructuralProcessNetwork.traceDenotation`, so it is not possible to project the field `traceDenotation` from an expression
  serverNetwork
of type
  StructuralProcessNetwork ProcessSpec requestOf
-/
#guard_msgs in
example := serverNetwork.traceDenotation

/--
error: Invalid field `exact`: The environment does not contain `Grass.Process.StructuralProcessNetwork.exact`, so it is not possible to project the field `exact` from an expression
  serverNetwork
of type
  StructuralProcessNetwork ProcessSpec requestOf
-/
#guard_msgs in
example := serverNetwork.exact

/--
error: Invalid field `channels`: The environment does not contain `Grass.Process.StructuralProcessNetwork.channels`, so it is not possible to project the field `channels` from an expression
  serverNetwork
of type
  StructuralProcessNetwork ProcessSpec requestOf
-/
#guard_msgs in
example := serverNetwork.channels

end Grass.Process.Tests.StructuralNetwork
