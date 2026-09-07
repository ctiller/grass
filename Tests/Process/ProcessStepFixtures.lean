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
* `answering_an_unissued_demand_is_unconstructible` is the same for the
  outstanding bag: a step cannot settle a demand the process never issued.

  A reviewer found this bullet naming an `an_unprojected_observation_is_unconstructible`
  the file does not contain and describing a claim it does not make. The trace
  half — that a step cannot append an observation the role did not make — is
  `StepsLocally.emittedIsProjected`, and it is checked by
  `Grass/Process/Trace/Linearization.lean` rather than refuted here.
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

/-- And after one tick: one lower, holding nothing, with a `beep` produced.

`pending`, not `observations`. A process step produces; only a commit publishes.
See `Grass/Process/Network/Assertion.lean`'s `NetworkFragment.pending`. -/
def busyAfter (remaining : Nat) : ServerWorld :=
  { quiet with
      instances := fun kind _ =>
        match kind with
        | .listener => some (settled remaining)
        | .connection => none
      pending := [Observation.beep] }

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
theorem the_listener_ticks (remaining : Nat) (running : remaining ≠ 0)
    (answer : countdownVocabulary.Result .tick) :
    serverPlan.StepsLocally (busy remaining) (busyAfter remaining) .listener ()
      (.result .tick answer) [Observation.beep] 0 [Observation.beep] where
  from' := ⟨awaiting remaining, rfl, trivial, rfl⟩
  stillLive := ⟨settled remaining, rfl, trivial⟩
  protocolStep :=
    ⟨awaiting remaining, settled remaining, rfl, rfl, rfl, rfl,
      ⟨running, rfl, rfl, rfl⟩, ⟨0, rfl, rfl⟩, rfl, rfl, rfl⟩
  emittedIsProjected := rfl
  producesPending := rfl
  writesPermitted := by
    intro region moved
    exact absurd rfl moved
  sharedWritesAdmitted := by
    intro region moved
    exact absurd rfl moved
  scope := by
    intro fragment outside
    cases fragment with
    | instanceState kind slot =>
      cases kind with
      | listener => exact absurd (Or.inl rfl) outside
      | connection => rfl
    | pending => exact absurd (Or.inr (Or.inl ⟨by simp, rfl⟩)) outside
    | _ => rfl

/-- So it is a transition of the plan, and one that emits. -/
def tickStep (remaining : Nat) (running : remaining ≠ 0)
    (answer : countdownVocabulary.Result .tick) :
    serverPlan.NetworkTransition (busy remaining) (busyAfter remaining) :=
  .processStep .listener () (.result .tick answer) [Observation.beep] 0
    [Observation.beep] (the_listener_ticks remaining running answer)

/-- **And it declares the pending trace, because it really moved it.** -/
theorem the_tick_emits (remaining : Nat) (running : remaining ≠ 0)
    (answer : countdownVocabulary.Result .tick) :
    (tickStep remaining running answer).scope .pending :=
  Or.inr (Or.inl ⟨by simp, rfl⟩)

/-- It writes no shared region, so the route-table immutability argument still applies. -/
theorem the_tick_writes_nothing (remaining : Nat) (running : remaining ≠ 0)
    (answer : countdownVocabulary.Result .tick) (region : serverTopology.SharedRegion) :
    ¬ (tickStep remaining running answer).scope (.region region) := by
  rintro (isSlot | ⟨_, isObservations⟩ | ⟨_, moved, _⟩)
  · exact absurd isSlot (by simp)
  · exact absurd isObservations (by simp)
  · exact absurd rfl moved

/-! ## And what it cannot be -/

/--
The world the listener would be in if a tick left its countdown alone: same
state, same outstanding bag, one `beep` on the trace.

The trace has to move, because `countdown.Step` on a `tick` result emits one —
so a fixture that held the trace still would be excluded by the observation
equation and would say nothing about the state. That is what an earlier version
of the next theorem did, and its "real side condition rather than true by luck"
docstring was the luck.
-/
def busyStuck (remaining : Nat) : ServerWorld :=
  { busy remaining with observations := [Observation.beep] }

/--
**A step that leaves the countdown where it was is unconstructible.**

What `protocolStep` bought. `countdown.Step` on a `tick` result demands
`after = state - 1`, and here the trace and the outstanding bag both move
exactly as the protocol says — so the state equation is the only obstruction
left and the `0 < remaining` side condition is load-bearing rather than
decorative. Before the field existed this had every other field and was
perfectly constructible.

`Nat` subtraction saturates, so at zero the claim is false and the hypothesis is
what says so.
-/
theorem a_step_that_does_not_tick_is_unconstructible (remaining : Nat)
    (positive : 0 < remaining) (answer : countdownVocabulary.Result .tick)
    (step : serverPlan.StepsLocally (busy remaining) (busyStuck remaining) .listener ()
      (.result .tick answer) [Observation.beep] 0 [Observation.beep]) : False := by
  obtain ⟨fromInstance, toInstance, _, _, foundFrom, foundTo, moved, _, _⟩ := step.protocolStep
  have found : (busy remaining).instances .listener () = some (awaiting remaining) := rfl
  have foundStuck : (busyStuck remaining).instances .listener () = some (awaiting remaining) := rfl
  rw [found] at foundFrom
  rw [foundStuck] at foundTo
  injection foundFrom with sameFrom
  injection foundTo with sameTo
  subst sameFrom
  subst sameTo
  obtain ⟨_, lowered, _, _⟩ := moved
  simp only [awaiting] at lowered
  omega

/--
**And a step answering a demand the listener never issued is unconstructible.**

§2's linearity at the network, and the reason `ProcessInstance.outstanding`
exists. `SettlesDemands` requires an answering event to remove exactly one
`cons` from the instance's bag, so a listener holding nothing cannot be told its
`tick` came back — `Bag.not_consume_zero` is the whole proof, and the after-world
is left arbitrary so that nothing else can be doing the work.

Before the field existed, `StepsLocally` required the protocol's `Step`
relation, obtained an issued bag from it, and discarded the bag. Nothing could
be outstanding at a network instance, so nothing could be answered wrongly
either.
-/
theorem answering_an_unissued_demand_is_unconstructible (remaining : Nat)
    (answer : countdownVocabulary.Result .tick) (after : ServerWorld)
    (step : serverPlan.StepsLocally (busyAfter remaining) after .listener ()
      (.result .tick answer) [Observation.beep] 0 [Observation.beep]) : False := by
  obtain ⟨fromInstance, toInstance, _, _, foundFrom, _, _, settles, _⟩ := step.protocolStep
  have isSettled : fromInstance = settled remaining := by
    have found : (busyAfter remaining).instances .listener () = some (settled remaining) := rfl
    rw [found] at foundFrom
    injection foundFrom with same
    exact same.symm
  subst isSettled
  obtain ⟨remainder, consumes, _⟩ := settles
  exact Bag.not_consume_zero consumes

/--
**And the tick preserves the incarnation's identity, which the step now says.**

The clause local adversarial review found missing: `ProcessInstance` has seven
fields and `protocolStep` constrained two, so a tick could move the listener to
a generation nothing allocated and re-parent it under another role while
`allocatedNominals` reported that the step allocated nothing. The reviewer built
that step and proved the network after it fails `NominalsAllocated` and
`ParentageValid`.

Read back off the step rather than off the two definitions, so it is the field
that is being checked and not the fixture's own arithmetic.
-/
theorem the_tick_preserves_the_incarnation (remaining : Nat) (running : remaining ≠ 0)
    (answer : countdownVocabulary.Result .tick) :
    ∃ (fromInstance toInstance : ProcessInstance serverTopology)
      (fromKind : fromInstance.kind = Role.listener) (toKind : toInstance.kind = Role.listener),
      toKind ▸ toInstance.ref = fromKind ▸ fromInstance.ref ∧
      toKind ▸ toInstance.parentage = fromKind ▸ fromInstance.parentage ∧
      toKind ▸ toInstance.request = fromKind ▸ fromInstance.request := by
  obtain ⟨fromInstance, toInstance, fromKind, toKind, _, _, _, _, sameRef, sameParent,
    sameRequest⟩ := (the_listener_ticks remaining running answer).protocolStep
  exact ⟨fromInstance, toInstance, fromKind, toKind, sameRef, sameParent, sameRequest⟩

/-! ## A step that writes a shared region

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.128 and `agent-bus` ruling
`g-design:84`. Until this section `ProcessPlan.sharedUpdate` was declared and
exercised nowhere: every `StepsLocally` in the corpus discharged
`writesPermitted` and `sharedWritesAdmitted` by `absurd rfl moved`, because no
fixture step moved a region at all. A bound nothing is held to is the shape this
ledger refuses, so here is a step held to it, and one refused by it.

`serverPlan.sharedUpdate` says the accept counter goes up by exactly one. The
listener may write it — `sharedAccess .listener .acceptCount` is `.readWrite` —
so the capability is not what decides these two cases; the *value* is.
-/

/-- The counter after one accept. -/
def busyCounted (remaining : Nat) : ServerWorld :=
  { busyAfter remaining with
      shared := fun
        | .routeTable => ⟨[]⟩
        | .acceptCount => ⟨1⟩ }

/-- And after a write that skips a number. -/
def busyMiscounted (remaining : Nat) : ServerWorld :=
  { busyAfter remaining with
      shared := fun
        | .routeTable => ⟨[]⟩
        | .acceptCount => ⟨7⟩ }

theorem the_counter_moved (remaining : Nat) :
    (busyAfter remaining).shared .acceptCount ≠ (busyCounted remaining).shared .acceptCount := by
  intro same
  have counts : (0 : Nat) = 1 := congrArg (fun held => held.down) same
  exact absurd counts (by decide)

/--
**A tick that also counts the accept is a step**, and `sharedWritesAdmitted` is
where it pays for the write.

Every other field is `the_listener_ticks`'s. What is new is the last two: the
counter moved, so `writesPermitted` needs the listener to have write access and
`sharedWritesAdmitted` needs the new value to be one the plan admits.
-/
theorem the_listener_counts (remaining : Nat) (running : remaining ≠ 0)
    (answer : countdownVocabulary.Result .tick) :
    serverPlan.StepsLocally (busy remaining) (busyCounted remaining) .listener ()
      (.result .tick answer) [Observation.beep] 0 [Observation.beep] where
  from' := ⟨awaiting remaining, rfl, trivial, rfl⟩
  stillLive := ⟨settled remaining, rfl, trivial⟩
  protocolStep :=
    ⟨awaiting remaining, settled remaining, rfl, rfl, rfl, rfl,
      ⟨running, rfl, rfl, rfl⟩, ⟨0, rfl, rfl⟩, rfl, rfl, rfl⟩
  emittedIsProjected := rfl
  producesPending := rfl
  writesPermitted := by
    intro region moved
    cases region with
    | routeTable => exact absurd rfl moved
    | acceptCount => rfl
  sharedWritesAdmitted := by
    intro region moved _ _ _ _ _ _
    cases region with
    | routeTable => exact absurd rfl moved
    | acceptCount => rfl
  scope := by
    intro fragment outside
    cases fragment with
    | instanceState kind slot =>
      cases kind with
      | listener => exact absurd (Or.inl rfl) outside
      | connection => rfl
    | region region =>
      cases region with
      | routeTable => rfl
      | acceptCount =>
        exact absurd (Or.inr (Or.inr ⟨.acceptCount, the_counter_moved remaining, rfl⟩)) outside
    | pending => exact absurd (Or.inr (Or.inl ⟨by simp, rfl⟩)) outside
    | _ => rfl

/--
**And the same step writing a value the plan does not admit is refused.**

The counter jumps from nothing to seven. `writesPermitted` is satisfied — the
listener may write this region — so the capability is not what refuses it;
`ProcessPlan.sharedUpdate` is, which is exactly the gap §10.103 recorded and
`g-design:84` ruled on. Before the field, this step was constructible and the
after-world passed every `WellFormed` clause.
-/
theorem the_listener_may_not_miscount (remaining : Nat)
    (answer : countdownVocabulary.Result .tick)
    (step : serverPlan.StepsLocally (busy remaining) (busyMiscounted remaining) .listener ()
      (.result .tick answer) [Observation.beep] 0 [Observation.beep]) : False := by
  have moved : (busy remaining).shared .acceptCount
      ≠ (busyMiscounted remaining).shared .acceptCount := by
    intro same
    have counts := congrArg (fun held => held.down) same
    simp [busy, busyMiscounted, Grass.Process.Tests.World.quiet] at counts
  have admitted := step.sharedWritesAdmitted .acceptCount moved
    (awaiting remaining) (settled remaining) rfl rfl rfl rfl
  have counts : (7 : Nat) = 0 + 1 := admitted
  exact absurd counts (by decide)

end Grass.Process.Tests.ProcessStep
