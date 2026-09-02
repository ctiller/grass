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
