import Grass.Process.Network.Assertion
import Grass.Process.Network.Escrow
import Grass.Process.Network.Instance
import Grass.Process.Observation

/-!
# The logical process network, and the agreement its assertions are framed over

`docs/DECISIONS.md` decision 128, ruling `agent-bus` issue `c-process:43`,
settles where the world comes from:

> The assertion must name the world it describes. That world cannot depend on a
> completed `ProcessPlan`, because channel contracts are themselves fields of
> the plan. Grass breaks the dependency at the smallest useful seam: the plan
> declares its per-edge message family before its contracts; topology plus that
> family is enough to define the whole logical-network carrier. Contracts are
> then stated over that carrier.

So this module is that seam. It takes a topology and a per-edge `Message`
family — the two things a plan has *before* its contracts — and builds the
carrier and the canonical `WorldAgreement` over it. `Channel.lean` states
contracts against that agreement, and `Plan.lean` closes the loop with
`ProcessPlan` and `LogicalProcessNetwork plan`.

`LogicalProcessNetworkCore` is a construction dependency, not a second public
network semantics. Authors and later theorems use `LogicalProcessNetwork plan`.

## `logicalWorldAgreement` is the point

`Grass/Process/Network/Assertion.lean` takes an agreement as an interface, and
its own note is blunt about the risk: a caller supplying equality satisfies
every law except `agreesGlue`, and under it every framing obligation collapses
to "the worlds are identical". `agreesGlue` is what excludes that, and it is a
real obligation — it says the named fragments are a complete, independent
decomposition of the world.

`logicalWorldAgreement` discharges it, and the shape of `Core` below is what
makes that possible rather than a coincidence. Every field is a function of the
index its fragment names: `instances` of a slot, `shared` of a region,
`inFlight` and `sessions` of an edge-and-session pair. The mixed world takes
each component from one side or the other according to whether its fragment is
inside the split, which is only writable because there is exactly one component
per fragment.

The construction decides an arbitrary predicate, so it is classical.
`Grass/Process/Network/Assertion.lean` itself is not — `agreesGlue` is a
hypothesis there — and this is the right place for the cost to land: the world
supplier pays, not the assertion language.

## Two divergences from the declared record, and why

`docs/PROCESS.md` §3 writes `instances : ... -> ProcessId kind -> Option
(ProcessInstance topology)`. `ProcessId` is declared nowhere in the corpus;
`ProcessRef` carries `instanceId : InstanceId kind`, so the slot type is
`InstanceId` and that is what this module uses. The generation lives in the
stored instance, not in the key, which is what makes one live incarnation per
slot and what `NetworkFragment.instanceState` is keyed by.

§3 writes `obligations : LogicalObligationLedger`. Obligations are not
`c-process`'s layer — `docs/MEMORY_IMPLEMENTATION_PLAN.md` puts them with the
memory owner — and `Grass/Process` reaching into another layer to state its own
world would be exactly the import edge `coord1:5`'s diamond exists to prevent.
So the ledger is a *parameter* here. A plan instantiates it at the real one, and
`Agrees` below treats it as one opaque fragment, which is all the
framing laws need.
-/

namespace Grass.Process

open Grass.Specification

universe u w v r m o

/--
One occurrence on one channel edge: a message of that edge's family, and an
occurrence of it.

The escrow ledger holds one occurrence type, so the message travels inside the
occurrence rather than indexing the ledger.
-/
abbrev EdgeOccurrence {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary)
    (Message : topology.ChannelKind → Type m) (edge : topology.ChannelKind) :
    Type (max m r) :=
  Sigma fun message : Message edge => topology.ChannelOccurrence edge message

/--
Whether a channel session is open, closed, or dead.

`docs/PROCESS.md` §3 distinguishes them — "ordinary close is distinct from
endpoint death" — and `Grass/Process/Network/Escrow.lean` gives an occurrence a
separate ending for each. A session's status is the endpoint-independent fact
those endings are about.
-/
inductive SessionStatus
  /-- Accepting sends. -/
  | open
  /-- Closed in the ordinary way. -/
  | closed
  /-- Died. -/
  | died
  deriving DecidableEq, Repr

/--
The logical world a plan steps through, before the plan exists.

`docs/PROCESS.md` §3's `LogicalProcessNetworkCore`, over the topology and the
per-edge message family — the two things decision 128 requires a plan to
declare before its contracts.

Every field is a function of the index that its `NetworkFragment` names. That is
not incidental: it is what lets `logicalWorldAgreement` below discharge
`agreesGlue`, and a world shaped otherwise could not.
-/
structure LogicalProcessNetworkCore {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary)
    (Message : topology.ChannelKind → Type m)
    (Obligations : Type o) : Type (max u w v r m o) where
  /-- The incarnation living in each slot, if any. -/
  instances : (kind : topology.ProcessKind) → topology.InstanceId kind →
    Option (ProcessInstance topology)
  /-- The contents of each shared region. -/
  shared : (region : topology.SharedRegion) → topology.SharedState region
  /-- What each session is holding in escrow. -/
  inFlight : (edge : topology.ChannelKind) → topology.ChannelId edge →
    EscrowLedger (EdgeOccurrence topology Message edge) (topology.ChannelId edge)
  /-- Whether each session is open, closed, or dead. -/
  sessions : (edge : topology.ChannelKind) → topology.ChannelId edge → SessionStatus
  /-- The obligation ledger, whose shape belongs to another layer. -/
  obligations : Obligations
  /-- The observations emitted so far, in order. -/
  observations : Trace boundary.Observation
  /-- Every nominal ever allocated. Freshness is absence from this. -/
  usedNominals : NominalHistory topology.Carrier

namespace LogicalProcessNetworkCore

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}
  {Message : topology.ChannelKind → Type m} {Obligations : Type o}

/-- Two networks agree on one fragment when they agree on the component it names. -/
def Agrees (fragment : NetworkFragment topology)
    (left right : LogicalProcessNetworkCore topology Message Obligations) : Prop :=
  match fragment with
  | .instanceState kind slot => left.instances kind slot = right.instances kind slot
  | .region region => left.shared region = right.shared region
  | .escrow edge session => left.inFlight edge session = right.inFlight edge session
  | .session edge session => left.sessions edge session = right.sessions edge session
  | .obligations => left.obligations = right.obligations
  | .observations => left.observations = right.observations
  | .nominals => left.usedNominals = right.usedNominals

theorem agrees_refl (fragment : NetworkFragment topology)
    (network : LogicalProcessNetworkCore topology Message Obligations) :
    Agrees fragment network network := by
  cases fragment <;> rfl

theorem agrees_symm (fragment : NetworkFragment topology)
    (left right : LogicalProcessNetworkCore topology Message Obligations) :
    Agrees fragment left right → Agrees fragment right left := by
  cases fragment <;> exact Eq.symm

theorem agrees_trans (fragment : NetworkFragment topology)
    (a b c : LogicalProcessNetworkCore topology Message Obligations) :
    Agrees fragment a b → Agrees fragment b c → Agrees fragment a c := by
  cases fragment <;> exact Eq.trans

open Classical in
/--
**The fragments decompose the world.**

The mixed network takes each component from `left` or from `right` according to
whether the fragment reading it is inside the split. Writable exactly because
`LogicalProcessNetworkCore` has one component per fragment family, indexed the
way its fragment is.

This is `WorldAgreement.agreesGlue`, and it is what stops a footprint from being
a decoration. See the module note.
-/
theorem agrees_glue (inside : NetworkFragment topology → Prop)
    (left right : LogicalProcessNetworkCore topology Message Obligations) :
    ∃ mixed,
      (∀ fragment, inside fragment → Agrees fragment mixed left) ∧
      (∀ fragment, ¬ inside fragment → Agrees fragment mixed right) := by
  refine ⟨{
    instances := fun kind slot =>
      if inside (.instanceState kind slot) then left.instances kind slot
      else right.instances kind slot
    shared := fun region =>
      if inside (.region region) then left.shared region else right.shared region
    inFlight := fun edge session =>
      if inside (.escrow edge session) then left.inFlight edge session
      else right.inFlight edge session
    sessions := fun edge session =>
      if inside (.session edge session) then left.sessions edge session
      else right.sessions edge session
    obligations := if inside .obligations then left.obligations else right.obligations
    observations :=
      if inside .observations then left.observations else right.observations
    usedNominals := if inside .nominals then left.usedNominals else right.usedNominals },
    ?_, ?_⟩
  · intro fragment member
    cases fragment <;> simp [Agrees, member]
  · intro fragment member
    cases fragment <;> simp [Agrees, member]

end LogicalProcessNetworkCore

/--
**The canonical agreement.**

`docs/PROCESS.md` §3: "The canonical `logicalWorldAgreement` decomposes exactly
the named network fragments and proves the gluing law, so an assertion footprint
is meaningful rather than a decoration."

A completed plan instantiates its channel contracts here. A reusable lower
module may still quantify over an arbitrary `WorldAgreement` —
`Grass/Process/Network/Assertion.lean` does — and that generality is what let the
assertion language be written before this module existed.
-/
noncomputable def logicalWorldAgreement {registry : ProtocolRegistry.{u, w, v}}
    {boundary : DriverBoundary.{u}}
    (topology : ProcessTopologyCore.{u, w, v, r} registry boundary)
    (Message : topology.ChannelKind → Type m) (Obligations : Type o) :
    WorldAgreement topology (LogicalProcessNetworkCore topology Message Obligations) where
  Agrees := LogicalProcessNetworkCore.Agrees
  agreesRefl := LogicalProcessNetworkCore.agrees_refl
  agreesSymm := LogicalProcessNetworkCore.agrees_symm
  agreesTrans := LogicalProcessNetworkCore.agrees_trans
  agreesGlue := LogicalProcessNetworkCore.agrees_glue

/-! ## What a well-formed network owes -/

namespace LogicalProcessNetworkCore

variable {registry : ProtocolRegistry.{u, w, v}} {boundary : DriverBoundary.{u}}
  {topology : ProcessTopologyCore.{u, w, v, r} registry boundary}
  {Message : topology.ChannelKind → Type m} {Obligations : Type o}
  (network : LogicalProcessNetworkCore topology Message Obligations)

/--
Every instance the network holds is in the slot it says it is.

Without it a slot could hold an incarnation whose own `ref` names a different
slot, and a lookup would disagree with the thing it found.
-/
def SlotsAgree : Prop :=
  ∀ kind slot incarnation, network.instances kind slot = some incarnation →
    incarnation.kind = kind

/--
**Every instance's stored ending is one its protocol reaches.**

`docs/DECISIONS.md` decision 129 puts this at the network: "Network
well-formedness ties a stored terminal result to the relational `Terminal`
witness." `Grass/Process/Network/Instance.lean` states the per-instance
predicate and says it cannot enforce it, having no network to enforce it over.
This is the enforcement.
-/
def LifecyclesWitnessed : Prop :=
  ∀ kind slot incarnation, network.instances kind slot = some incarnation →
    incarnation.LifecycleWitnessed

/--
**There is exactly one root incarnation.**

Decision 130 puts root uniqueness at the network rather than on each instance's
author, and this is it: at most one instance claims `ProcessParentage.root`.
Existence is a separate matter, since a network between transitions may hold
none.
-/
def RootUnique : Prop :=
  ∀ leftKind leftSlot leftInstance rightKind rightSlot rightInstance,
    network.instances leftKind leftSlot = some leftInstance →
    network.instances rightKind rightSlot = some rightInstance →
    leftInstance.IsRoot → rightInstance.IsRoot →
    leftKind = rightKind

/--
Everything a network must satisfy before its assertions mean anything.

Gathered rather than scattered, so `Plan.lean` and `Transition.lean` have one
name to require and a reader has one place to look.
-/
structure WellFormed
    (network : LogicalProcessNetworkCore topology Message Obligations) : Prop where
  /-- Slots hold what they say they hold. -/
  slotsAgree : network.SlotsAgree
  /-- Stored endings are endings the protocol reaches. -/
  lifecyclesWitnessed : network.LifecyclesWitnessed
  /-- At most one root. -/
  rootUnique : network.RootUnique

/-- A terminated instance in a well-formed network yields its exact result. -/
theorem terminated_result_is_exact
    {network : LogicalProcessNetworkCore topology Message Obligations}
    (wellFormed : network.WellFormed) {kind slot incarnation}
    (found : network.instances kind slot = some incarnation)
    {result : (topology.protocol incarnation.kind).TerminalResult}
    (ended : incarnation.lifecycle = .terminated result) :
    (topology.protocol incarnation.kind).Terminal
      incarnation.request incarnation.localState result :=
  incarnation.terminated_result_is_exact
    (wellFormed.lifecyclesWitnessed kind slot incarnation found) ended

end LogicalProcessNetworkCore

end Grass.Process
