import Grass.Process.Network.Instance
import Tests.Process.M2GraphFixtures

/-!
# What an instance says about its own ending, and about its parent

`Grass/Process/Network/Instance.lean` is the second revision of two types the
corpus named and did not declare, and both revisions were forced by a defect
this file now pins.

## The lifecycle

`LifecycleWitnessed` must have teeth — an instance tagged `terminated` whose
state is not terminal must fail it (`terminated_at_three_is_not_witnessed`) —
and must be satisfiable (`terminated_at_zero_is_witnessed`).

Its *job* is what changed. Under the payload-free predecessor it was the only
way to learn what a process answered, and it could not do that: `Terminal` is a
relation, so it produced *some* result rather than *the* one the parent
recorded. `blind_result_is_not_determined` is that defect, still visible: at a
protocol whose terminal states ignore the answer, the *state* is terminal for
`true` and for `false` alike. Under decision 129 the tag stores the result, so
the ending is exact regardless, and `blindRoot_ending_is_exact` is that — the
same protocol, the same ambiguous state, and one unambiguous ending.

## The parentage

`root_and_detached_are_distinguishable` is decision 130's payoff. Under the
`Option` this replaces, a detached child's `parent` was `none` exactly as a
root's was: "the root is the instance with no parent" was false as a network
law, and `Grass/Process/Network/Child.lean`'s `NonReturningReason.detached` was
unjustifiable from state. Now `detach` keeps the former parent while dropping
its authority, and `detached_keeps_its_history` is that.

The `countdown` topology is `Tests/Process/M2GraphFixtures.lean`'s. The second
topology exists because `countdown` cannot show the result question at all: its
`TerminalResult` is `ULift Unit`, so any uniqueness holds for want of a second
value rather than because the protocol determines anything.
-/

namespace Grass.Process.Tests.Instances

open Grass.Process
open Grass.Process.Tests
open Grass.Specification

/-! ## Teeth, at the countdown topology -/

/-- The listener incarnation this connection was spawned by. -/
def listenerZero : serverTopology.ProcessRef .listener where
  instanceId := ()
  generation := ⟨.processGeneration, 0⟩
  isGeneration := rfl

/-- A connection incarnation, mid-countdown at three. -/
def counting : ProcessInstance serverTopology where
  kind := .connection
  ref := connectionSeven 0
  parentage := .attached .listener listenerZero
  request := ⟨3⟩
  localState := ⟨3⟩
  outstanding := 0
  lifecycle := .running

/-- The same incarnation, finished. -/
def finished : ProcessInstance serverTopology :=
  { counting with localState := ⟨0⟩, lifecycle := .terminated ⟨()⟩ }

/-- And the lie: tagged terminated while still counting. -/
def lying : ProcessInstance serverTopology :=
  { counting with lifecycle := .terminated ⟨()⟩ }

/--
**A running process cannot be tagged terminated.**

`lying` differs from `counting` only in its tag, and that is enough to make it
not witnessed — so a network carrying `LifecycleWitnessed` cannot contain it.
This is what shows the predicate is not universally true.
-/
theorem terminated_at_three_is_not_witnessed : ¬ lying.LifecycleWitnessed := by
  intro witnessed
  have terminal := witnessed ⟨()⟩ rfl
  have counted : ¬ ((3 : Nat) = 0) := by decide
  exact counted terminal

/-- A genuinely finished process is witnessed, so the predicate is satisfiable. -/
theorem terminated_at_zero_is_witnessed : finished.LifecycleWitnessed :=
  fun _ _ => rfl

/-- A running process is witnessed vacuously, and is not thereby terminal. -/
theorem counting_is_witnessed : counting.LifecycleWitnessed :=
  ProcessInstance.live_witnessed_vacuously trivial

/-! ## Liveness -/

/-- A process under an unacknowledged cancellation request is running. -/
theorem counting_is_live : counting.Live := trivial

/-- A finished one is not, by way of the enumeration rather than by reduction. -/
theorem finished_is_not_live : ¬ finished.Live := by
  intro live
  have running : finished.lifecycle = ProcessLifecycle.running :=
    ProcessLifecycle.live_iff_running.mp live
  exact absurd running (by simp [finished, counting])

/-! ### The enumeration is closed where it says it is

`cancelled` is a state; "cancelling" is not, because a process under an
unacknowledged request is still `running`. `detached` is not a state either —
detachment is `ProcessParentage`'s, not the lifecycle's. Both guards fail if
anyone adds the constructor.
-/

/--
error: Unknown constant `Grass.Process.ProcessLifecycle.cancelling`

Note: Inferred this name from the expected resulting type of `.cancelling`:
  ProcessLifecycle countdownLifted
-/
#guard_msgs in
example : ProcessLifecycle countdownLifted := .cancelling

/--
error: Unknown constant `Grass.Process.ProcessLifecycle.detached`

Note: Inferred this name from the expected resulting type of `.detached`:
  ProcessLifecycle countdownLifted
-/
#guard_msgs in
example : ProcessLifecycle countdownLifted := .detached

/-! ## A topology where the result question is visible

Two protocols over one vocabulary. `blind` reaches a terminal state without its
result mattering; `determined` reaches one only with the answer `true`. Nothing
else about them differs.
-/

/-- Two roles, one per protocol. -/
inductive Answerer
  | blind
  | determined
  deriving DecidableEq, Repr

/-- Terminal at zero, for either answer. -/
@[reducible] def blindSpec : ProcessSpec.{0, 1} where
  vocabulary := countdownVocabulary
  Request := ULift Nat
  State := ULift Nat
  TerminalResult := ULift Bool
  Initial := fun request state _ _ => request.down = state.down
  Terminal := fun _ state _ => state.down = 0
  Step := fun _ _ _ _ _ => False
  view := none

/-- Terminal at zero, and only with `true`. -/
@[reducible] def determinedSpec : ProcessSpec.{0, 1} where
  vocabulary := countdownVocabulary
  Request := ULift Nat
  State := ULift Nat
  TerminalResult := ULift Bool
  Initial := fun request state _ _ => request.down = state.down
  Terminal := fun _ state result => state.down = 0 ∧ result.down = true
  Step := fun _ _ _ _ _ => False
  view := none

/-- The blind protocol faces the boundary; the exposure is `countdown`'s. -/
@[reducible] def answerExposure :
    ProtocolExposesBoundary blindSpec fixtureBoundary where
  deliver := id
  exportDemand := some
  accept := fun equal result => by
    cases equal
    exact result
  observe := some

/-- The scope this fixture's second registry fragment owns. -/
@[reducible] def answerScope : ScopeId := ⟨["Tests", "Process", "Answer"]⟩

/-- Two keys, two protocols. -/
@[reducible] def answerRegistry : ProtocolRegistry.{0, 1, 0} :=
  (⟨answerScope, Answerer, fun
      | .blind => blindSpec
      | .determined => determinedSpec⟩ :
    RegistryFragment.{0, 1, 0}).toRegistry

/-- No shared state and no channels; this graph is about protocols. -/
@[reducible] def answerGraph :
    ProcessGraph.{0, 1, 0, 0} answerRegistry fixtureBoundary where
  ProcessKind := Answerer
  SharedRegion := Empty
  SharedState := fun region => region.elim
  protocolKey := id
  root := .blind
  rootBoundary := answerExposure
  observeAt := fun kind =>
    match kind with
    | .blind => some
    | .determined => fun _ => none
  observeAtRoot := rfl
  maySpawn := fun parent child => parent = .blind ∧ child = .determined
  sharedAccess := fun _ region => region.elim
  population :=
    { bound := fun
        | .blind => .exactlyOne
        | .determined => .boundedByResourcePolicy
      identity := fun
        | .blind => .static
        | .determined => .generational }

@[reducible] def answerTopology :
    ProcessTopologyCore.{0, 1, 0, 0} answerRegistry fixtureBoundary where
  toProcessGraph := answerGraph
  Carrier := Nat
  carrierDecidableEq := inferInstance
  InstanceId := fun _ => Unit
  ChannelKind := Empty
  endpoints := fun edge => edge.elim
  spawnAuthority := fun _ _ _ _ _ => True

/-- A reference for either role; there is one incarnation of each here. -/
@[reducible] def answerRef (kind : Answerer) : answerTopology.ProcessRef kind where
  instanceId := ()
  generation := ⟨.processGeneration, 0⟩
  isGeneration := rfl

/-- The root, finished, at a protocol whose terminal states ignore the answer. -/
def blindRoot : ProcessInstance answerTopology where
  kind := .blind
  ref := answerRef .blind
  parentage := .root
  request := ⟨0⟩
  localState := ⟨0⟩
  outstanding := 0
  lifecycle := .terminated ⟨true⟩

/-- A child of it, finished, at the protocol that pins the answer. -/
def determinedChild : ProcessInstance answerTopology where
  kind := .determined
  ref := answerRef .determined
  parentage := .attached .blind (answerRef .blind)
  request := ⟨0⟩
  localState := ⟨0⟩
  outstanding := 0
  lifecycle := .terminated ⟨true⟩

/-- The same child, detached. -/
def detachedChild : ProcessInstance answerTopology := determinedChild.detach

/-! ### The state is ambiguous; the ending is not -/

/--
**The state alone does not determine the answer.**

`ProcessSpec.Terminal` is a relation. At `blindSpec` a state is terminal for
`true` and for `false` alike, so a payload-free tag plus the state could only
have produced *an* answer — possibly not the one the parent's transition
received. This is the defect decision 129 closes, and it is still exhibitable
because it is a fact about the protocol, not about the tag.
-/
theorem blind_result_is_not_determined :
    (answerTopology.protocol blindRoot.kind).Terminal
      blindRoot.request blindRoot.localState ⟨true⟩ ∧
    (answerTopology.protocol blindRoot.kind).Terminal
      blindRoot.request blindRoot.localState ⟨false⟩ :=
  ⟨rfl, rfl⟩

/-- The instance is witnessed: the answer it stores is one the protocol reaches. -/
theorem blindRoot_is_witnessed : blindRoot.LifecycleWitnessed := by
  intro result stored
  have isTrue : result = ⟨true⟩ := by
    injection stored with stored
    exact stored.symm
  rw [isTrue]
  rfl

/--
**And the ending is exact anyway.**

The same ambiguous state, and one unambiguous ending, because the tag carries
it. This is what decision 129 buys: an audit reading network state learns what
the process answered without replaying the parent's transition.
-/
theorem blindRoot_ending_is_exact :
    (answerTopology.protocol blindRoot.kind).Terminal
      blindRoot.request blindRoot.localState ⟨true⟩ :=
  blindRoot.terminated_result_is_exact blindRoot_is_witnessed rfl

/--
A network cannot store an answer the protocol never reaches from that state.

The half a stored payload cannot check for itself, and what `LifecycleWitnessed`
is now for: at `determinedSpec` only `true` is terminal, so an instance storing
`false` fails it.
-/
theorem determined_cannot_store_false :
    ¬ ({ determinedChild with lifecycle := .terminated ⟨false⟩ } :
        ProcessInstance answerTopology).LifecycleWitnessed := by
  intro witnessed
  have terminal := witnessed ⟨false⟩ rfl
  exact absurd terminal.2 (by decide)

/-! ### Root and detached are distinguishable -/

/-- The root is the root, by construction of its parentage. -/
theorem blindRoot_is_root : blindRoot.IsRoot := trivial

/--
**A root and a detached child are told apart.**

The defect decision 130 closes. Under the `Option` both had `parent = none`.
-/
theorem root_and_detached_are_distinguishable :
    blindRoot.IsRoot ∧ ¬ detachedChild.IsRoot ∧ detachedChild.IsDetached :=
  ⟨trivial, fun isRoot => isRoot, trivial⟩

/--
**Detaching drops authority and keeps the history.**

`docs/PROCESS.md` §3's "changes only `.attached parent` to `.detached parent`,
proves the references identical". The former parent is still there, which is
what makes `Child.lean`'s `NonReturningReason.detached` checkable against state.
-/
theorem detached_keeps_its_history :
    detachedChild.parentage.currentParent = none ∧
      detachedChild.parentage.knownParent = some ⟨.blind, answerRef .blind⟩ :=
  ⟨rfl, rfl⟩

/-- The attached child still has authority over it. -/
theorem attached_child_has_a_parent :
    determinedChild.parentage.currentParent = some ⟨.blind, answerRef .blind⟩ := rfl

/-- Detaching changes nothing about the run. -/
theorem detaching_preserves_the_run :
    detachedChild.lifecycle = determinedChild.lifecycle :=
  (determinedChild.detach_preserves_run).2

end Grass.Process.Tests.Instances
