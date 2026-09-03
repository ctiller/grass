import Tests.Process.TransitionFixtures

/-!
# A process step that is actually a protocol step

Every other fixture in this corpus that mentions `NetworkTransition.processStep`
pattern-matches on it. **None constructs one**, and that is how
`Grass/Process/Network/Transition.lean`'s `StepsLocally` went four revisions
claiming in its docstring that "its private state moves by the protocol's own
`Step` relation" while having no field that required it. Its `event` parameter
was used nowhere, there was no issued-demand bag, and the instance's new state
was arbitrary as long as it was live.

A structure nobody instantiates is a structure whose fields nobody misses. This
file instantiates it.

* `the_listener_ticks` is the positive witness: a live listener partway through
  its countdown consumes a `tick` result, moves to the next state *by
  `countdown.Step`*, issues nothing, and emits one `beep` that reaches the
  network trace through `ProcessGraph.observeAt`.
* `a_step_that_does_not_tick_is_unconstructible` is the negative one, and it is
  what the missing field cost. Before `protocolStep` existed this was provable
  in the wrong direction — a "process step" could leave the countdown where it
  was, or move it anywhere at all.
* `an_unprojected_observation_is_unconstructible` is the same for the trace: a
  step cannot append an observation the role did not make.
-/

namespace Grass.Process.Tests.ProcessStep

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld quiet)
open Grass.Process.Tests.Transition (serverPlan)

/-! ## A live listener -/

/--
The listener, partway through its countdown, waiting on one `tick`.

The outstanding bag is the point of the pair below. §2's run relation is linear
in demand multiplicity, and `StepsLocally.protocolStep` now carries that
equation at the network — so a listener that answers a `tick` must have had one
outstanding, and after answering it does not.
-/
def awaiting (remaining : Nat) : ProcessInstance serverTopology where
  kind := .listener
  ref := Instances.listenerZero
  parentage := .root
  request := ⟨3⟩
  localState := ⟨remaining⟩
  outstanding := Bag.ofList [Demand.tick]
  lifecycle := .running

/-- The same listener after the tick was answered: one lower, and holding nothing. -/
def settled (remaining : Nat) : ProcessInstance serverTopology where
  kind := .listener
  ref := Instances.listenerZero
  parentage := .root
  request := ⟨3⟩
  localState := ⟨remaining - 1⟩
  outstanding := 0
  lifecycle := .running

/-- The network with the waiting listener live and nothing else going on. -/
def busy (remaining : Nat) : ServerWorld :=
  { quiet with
      instances := fun kind _ =>
        match kind with
        | .listener => some (awaiting remaining)
        | .connection => none }

/-- And after one tick: one lower, holding nothing, with a `beep` in the trace. -/
def busyAfter (remaining : Nat) : ServerWorld :=
  { quiet with
      instances := fun kind _ =>
        match kind with
        | .listener => some (settled remaining)
        | .connection => none
      observations := [Observation.beep] }

theorem busy_holds_the_listener (remaining : Nat) :
    (busy remaining).instances .listener () = some (awaiting remaining) := rfl

theorem busy_starts_quiet (remaining : Nat) : (busy remaining).observations = [] := rfl

/-- **And it really is holding one outstanding demand.** -/
theorem the_listener_is_waiting (remaining : Nat) :
    (awaiting remaining).outstanding = Bag.ofList [Demand.tick] := rfl

/-! ## The step -/

/--
**A tick is a process step.**

Every field of `StepsLocally` at a concrete pair of worlds, and the one that
matters is `protocolStep`: the listener's private state moves from `remaining`
to `remaining - 1` because `countdown.Step` says a `tick` result does that, not
because this fixture asserted it.
-/
theorem the_listener_ticks (remaining : Nat)
    (answer : countdownVocabulary.Result .tick) :
    serverPlan.StepsLocally (busy remaining) (busyAfter remaining) .listener ()
      (.result .tick answer) (fun _ => False) [Observation.beep] 0
      [Observation.beep] where
  from' := ⟨awaiting remaining, rfl, trivial, rfl⟩
  stillLive := ⟨settled remaining, rfl, trivial⟩
  protocolStep :=
    ⟨awaiting remaining, settled remaining, rfl, rfl, rfl, rfl,
      ⟨rfl, rfl, rfl⟩, ⟨0, rfl, rfl⟩⟩
  emittedIsProjected := rfl
  observationsExtend := rfl
  writesPermitted := by
    intro region wrote
    exact absurd wrote id
  scope := by
    intro fragment outside
    cases fragment with
    | instanceState kind slot =>
      cases kind with
      | listener => exact absurd (Or.inl rfl) outside
      | connection => rfl
    | observations => exact absurd (Or.inr (Or.inl ⟨by simp, rfl⟩)) outside
    | _ => rfl

/-- So it is a transition of the plan, and one that emits. -/
def tickStep (remaining : Nat) (answer : countdownVocabulary.Result .tick) :
    serverPlan.NetworkTransition (busy remaining) (busyAfter remaining) :=
  .processStep .listener () (.result .tick answer) (fun _ => False) [Observation.beep] 0
    [Observation.beep] (the_listener_ticks remaining answer)

/-- **And it declares the trace, because it really moved it.** -/
theorem the_tick_emits (remaining : Nat) (answer : countdownVocabulary.Result .tick) :
    (tickStep remaining answer).scope .observations :=
  Or.inr (Or.inl ⟨by simp, rfl⟩)

/-- It writes no shared region, so the route-table immutability argument still applies. -/
theorem the_tick_writes_nothing (remaining : Nat)
    (answer : countdownVocabulary.Result .tick) (region : serverTopology.SharedRegion) :
    ¬ (tickStep remaining answer).scope (.region region) := by
  rintro (isSlot | ⟨_, isObservations⟩ | ⟨_, wrote, _⟩)
  · exact absurd isSlot (by simp)
  · exact absurd isObservations (by simp)
  · exact absurd wrote id

/-! ## And what it cannot be -/

/--
**A step that leaves the countdown where it was is unconstructible.**

What `protocolStep` bought. `countdown.Step` on a `tick` result demands
`after = state - 1`, so a `StepsLocally` from `busy remaining` to `busy
remaining` on that event has no `protocolStep` witness — and before the field
existed, it had every other field and was perfectly constructible.

Stated at a `remaining` where `remaining - 1 ≠ remaining`, because `Nat`
subtraction saturates and the claim is false at zero. That is itself worth
having in the fixture: the negative case has a real side condition rather than
being true by luck.
-/
theorem a_step_that_does_not_tick_is_unconstructible (remaining : Nat)
    (positive : 0 < remaining) (answer : countdownVocabulary.Result .tick)
    (step : serverPlan.StepsLocally (busy remaining) (busy remaining) .listener ()
      (.result .tick answer) (fun _ => False) [] 0 []) : False := by
  obtain ⟨fromInstance, toInstance, _, _, foundFrom, foundTo, moved, _⟩ := step.protocolStep
  rw [busy_holds_the_listener] at foundFrom foundTo
  injection foundFrom with sameFrom
  injection foundTo with sameTo
  subst sameFrom
  subst sameTo
  obtain ⟨lowered, _, _⟩ := moved
  simp only [awaiting] at lowered
  omega

/--
**And a step answering a demand the listener never issued is unconstructible.**

§2's linearity at the network, and the reason `ProcessInstance.outstanding`
exists. `SettlesDemands` requires an answering event to remove exactly one
`cons` from the instance's bag, so a listener holding nothing cannot be told its
`tick` came back — `Bag.not_consume_zero` is the whole proof.

Before the field existed, `StepsLocally` required the protocol's `Step`
relation, obtained an issued bag from it, and discarded the bag. Nothing could
be outstanding at a network instance, so nothing could be answered wrongly
either.
-/
theorem answering_an_unissued_demand_is_unconstructible (remaining : Nat)
    (answer : countdownVocabulary.Result .tick) (after : ServerWorld)
    (step : serverPlan.StepsLocally (busyAfter remaining) after .listener ()
      (.result .tick answer) (fun _ => False) [] 0 []) : False := by
  obtain ⟨fromInstance, toInstance, _, _, foundFrom, _, _, settles⟩ := step.protocolStep
  have isSettled : fromInstance = settled remaining := by
    have found : (busyAfter remaining).instances .listener () = some (settled remaining) := rfl
    rw [found] at foundFrom
    injection foundFrom with same
    exact same.symm
  subst isSettled
  obtain ⟨remainder, consumes, _⟩ := settles
  exact Bag.not_consume_zero consumes

/--
**And a step cannot append an observation the role did not make.**

`emittedIsProjected` at work: what reaches the network trace is the image of the
protocol's own segment under `ProcessGraph.observeAt`. A step whose protocol
emitted nothing cannot put a `beep` in the trace.
-/
theorem an_unprojected_observation_is_unconstructible (remaining : Nat)
    (event : (serverTopology.protocol .listener).Event)
    (step : serverPlan.StepsLocally (busy remaining) (busyAfter remaining) .listener ()
      event (fun _ => False) [Observation.beep] 0 []) : False := by
  have projected : [Observation.beep] = [] := step.emittedIsProjected
  exact absurd projected (by simp)

end Grass.Process.Tests.ProcessStep
