import Grass.Process.Network.Instance
import Tests.Process.M2GraphFixtures

/-!
# A lifecycle tag that a network cannot lie with — and the two things it cannot say

`Grass/Process/Network/Instance.lean` claims that `terminated` is a claim *about
the state*, so nothing is lost by leaving the result off the tag. That claim has
a precondition the module states and this fixture is here to make concrete.

* `LifecycleWitnessed` has teeth: an instance tagged `terminated` whose state is
  not terminal fails it. `terminated_at_three_is_not_witnessed`.
* It is satisfiable: a genuinely finished instance meets it and yields a result.
  `terminated_at_zero_is_witnessed`.
* **But `terminated_has_result` recovers *a* result, not *the* result.**
  `ProcessSpec.Terminal` is a relation, so at a protocol whose terminal states
  do not determine the answer, two different results are both recovered:
  `blind_result_is_not_determined`. At a protocol whose terminal states do
  determine it, they agree: `determined_result_is_unique`. That contrast is the
  whole content of the module's payload-free argument, and neither half is
  visible at `countdown`, whose `TerminalResult` is a singleton.

It also pins the parenthood distinction the module makes:

* `HasNoParent` is not `IsRoot`. A detached child has no parent and is not the
  root, and `detached_child_is_not_root` is that.

The `countdown` topology is `Tests/Process/M2GraphFixtures.lean`'s. The second
topology exists only because `countdown` cannot show the result question at all:
its `TerminalResult` is `ULift Unit`, so uniqueness holds for want of a second
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
  parent := some ⟨.listener, listenerZero⟩
  request := ⟨3⟩
  localState := ⟨3⟩
  lifecycle := .running

/-- The same incarnation, finished. -/
def finished : ProcessInstance serverTopology :=
  { counting with localState := ⟨0⟩, lifecycle := .terminated }

/-- And the lie: tagged terminated while still counting. -/
def lying : ProcessInstance serverTopology :=
  { counting with lifecycle := .terminated }

/--
**A running process cannot be tagged terminated.**

`lying` differs from `counting` only in its tag, and that is enough to make it
not witnessed — so a network carrying `LifecycleWitnessed` cannot contain it.
This is what shows the predicate is not universally true.
-/
theorem terminated_at_three_is_not_witnessed : ¬ lying.LifecycleWitnessed := by
  intro witnessed
  obtain ⟨_, terminal⟩ := witnessed rfl
  have counted : ¬ ((3 : Nat) = 0) := by decide
  exact counted terminal

/-- A genuinely finished process is witnessed, so the predicate is satisfiable. -/
theorem terminated_at_zero_is_witnessed : finished.LifecycleWitnessed :=
  fun _ => ⟨⟨()⟩, rfl⟩

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
  exact absurd running (by decide)

/-! ### The enumeration is closed where it says it is

`cancelled` is a state; "cancelling" is not, because a process under an
unacknowledged request is still `running`. `detached` is not a state either,
because `detach` changes `parent` rather than liveness. Both guards fail if
anyone adds the constructor.
-/

/--
error: Unknown constant `Grass.Process.ProcessLifecycle.cancelling`

Note: Inferred this name from the expected resulting type of `.cancelling`:
  ProcessLifecycle
-/
#guard_msgs in
example : ProcessLifecycle := .cancelling

/--
error: Unknown constant `Grass.Process.ProcessLifecycle.detached`

Note: Inferred this name from the expected resulting type of `.detached`:
  ProcessLifecycle
-/
#guard_msgs in
example : ProcessLifecycle := .detached

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
  parent := none
  request := ⟨0⟩
  localState := ⟨0⟩
  lifecycle := .terminated

/-- A child of it, finished, at the protocol that pins the answer. -/
def determinedChild : ProcessInstance answerTopology where
  kind := .determined
  ref := answerRef .determined
  parent := some ⟨.blind, answerRef .blind⟩
  request := ⟨0⟩
  localState := ⟨0⟩
  lifecycle := .terminated

/-- The same child, detached: its parent is gone from the record. -/
def detachedChild : ProcessInstance answerTopology :=
  { determinedChild with parent := none }

/-! ### The result is recovered, but not determined -/

/--
**Both answers are recovered from the same terminated instance.**

`ProcessSpec.Terminal` is a relation. At `blindSpec` a state is terminal for
`true` and for `false` alike, so `terminated_has_result` returns whichever the
proof happened to name — and a join reading it could hand back an answer the
parent's own transition never received.

This is the precondition the module's payload-free argument needs and does not
have in general. An earlier revision of that module claimed there was "only one
record" of the result with no such hypothesis; there is one record of *whether*
it finished, and none of *what it answered*.
-/
theorem blind_result_is_not_determined :
    blindRoot.TerminatedWith ⟨true⟩ ∧ blindRoot.TerminatedWith ⟨false⟩ :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- So the tag is witnessed twice over, by two disagreeing answers. -/
theorem blind_is_witnessed : blindRoot.LifecycleWitnessed :=
  ProcessInstance.terminatedWith_witnessed blind_result_is_not_determined.1

/--
**Where the terminal relation is functional, the recovered result is the
result.**

`determinedSpec` is terminal only with `true`, so any result the state is
terminal for equals the one a parent recorded. This is
`terminated_result_unique`'s hypothesis discharged concretely, and it is what
`Grass/Process/Spec.lean`'s `DeterministicProcess.terminal_functional` supplies
for the deterministic construction.
-/
theorem determined_result_is_unique
    (recovered : (answerTopology.protocol determinedChild.kind).TerminalResult)
    (terminal : (answerTopology.protocol determinedChild.kind).Terminal
      determinedChild.request determinedChild.localState recovered) :
    recovered = ⟨true⟩ := by
  obtain ⟨_, isTrue⟩ := terminal
  cases recovered
  simp_all
  rfl

/-- And the false answer is not available there, which is the contrast. -/
theorem determined_rejects_false : ¬ determinedChild.TerminatedWith ⟨false⟩ := by
  rintro ⟨_, _, isTrue⟩
  exact absurd isTrue (by decide)

/-! ### A detached child is not the root -/

/-- The root is the root: its kind faces the boundary and it has no parent. -/
theorem blindRoot_is_root : blindRoot.IsRoot := ⟨rfl, rfl⟩

/--
**A detached child has no parent and is not the root.**

`docs/PROCESS.md` §3 detaches children, and a detached child's `parent` is
`none` exactly as a root's is. `HasNoParent` holds of both; `IsRoot` does not,
because the kind is the load-bearing half. An earlier revision of the module
defined `IsRoot` as the absent parent alone, which made this instance a root.
-/
theorem detached_child_is_not_root :
    detachedChild.HasNoParent ∧ ¬ detachedChild.IsRoot := by
  refine ⟨rfl, ?_⟩
  rintro ⟨isRootKind, _⟩
  exact absurd isRootKind (by decide)

/-- The child that is still attached has a parent, so neither holds of it. -/
theorem determinedChild_has_a_parent : ¬ determinedChild.HasNoParent := by
  intro noParent
  exact absurd noParent (by simp [ProcessInstance.HasNoParent, determinedChild])

end Grass.Process.Tests.Instances
