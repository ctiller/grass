import Grass.Process.Network.Transition
import Tests.Process.ChannelFixtures

/-!
# A plan, and a step of it

`Grass/Process/Network/Transition.lean` says what one step of a logical process
network is, over an abstract plan. This file builds a plan — the first one, at
the M2 fixture topology — and takes a step of it.

What it pins:

* `serverPlan` exists. `ProcessPlan` ties a topology, a message family, the send
  and receive relations, and a contract per edge into one object at the
  canonical agreement for the full network. Until now nothing had shown the four
  could be satisfied together.
* `receiving_resolves_the_escrow` builds a `ResolvesEscrow`: an occurrence that
  was outstanding is now `received`, the ledger only moved forward, and nothing
  outside that session's escrow changed.
* `cannot_receive_twice` is the teeth — an occurrence already ended cannot be
  the subject of another resolution, which is the affine half of `docs/PROCESS.md`
  §3's resolve token stated at the step rather than at the ledger.
* `observations_did_not_move` reads the scope back out: the step's own
  `TouchesOnly` proof says the observation trace is unchanged, so a weave
  invariant over observations frames past this step without knowing what it was.

The ledgers here decide occurrence equality classically. Occurrences are
`LogicalNominal`-indexed sigma types with no `DecidableEq`, and the alternative
— a uniform `resolution` — cannot satisfy `noFabrication`, since it would claim
to have ended occurrences the ledger never escrowed.
-/

namespace Grass.Process.Tests.Transition

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld NoObligations quiet)
open Grass.Process.Tests.Channel (ServerMessage wire liveSteps liveChannel)

/--
The plan.

Its `steps` and `channel` are `Tests/Process/ChannelFixtures.lean`'s, which is
the point: the contract that file checks in isolation is the contract this plan
installs, at the same agreement.
-/
noncomputable def serverPlan : ProcessPlan graphRegistry fixtureBoundary NoObligations where
  topology := serverTopology
  message := World.serverMessage
  steps := fun _ => liveSteps
  channel := fun _ => liveChannel
  sessionOpenIsRecorded := fun _ _ _ open' => open'
  escrowImpliesOutstanding := fun _ _ _ _ escrowed => escrowed

/-- The world a step of it moves through is the one the other fixtures use. -/
theorem plan_world_is_the_fixture_world :
    serverPlan.LogicalProcessNetwork = ServerWorld := rfl

/-! ## One occurrence, in flight and then received -/

/-- The payload. -/
def payload : ServerMessage := ⟨7⟩

/-- Its occurrence on `wire`. -/
def occurrenceOf : serverTopology.ChannelOccurrence () payload :=
  ⟨wire, { id := ⟨.messageOccurrence, 0⟩, isMessage := rfl }⟩

/-- The escrow entry it becomes. -/
def escrowed : EdgeOccurrence serverTopology World.serverMessage () :=
  ⟨payload, occurrenceOf⟩

open Classical in
/-- A ledger holding it, in flight. -/
noncomputable def pendingLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun _ => none
  noFabrication := by simp
  coalesceCarrierLater := by simp
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by simp

open Classical in
/-- And the same ledger after the receiver consumed it. -/
noncomputable def settledLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun occurrence => if occurrence = escrowed then some .received else none
  noFabrication := by
    intro occurrence resolved
    by_cases isIt : occurrence = escrowed
    · simp [isIt]
    · simp [isIt] at resolved
  coalesceCarrierLater := by
    intro occurrence carrier merged
    by_cases isIt : occurrence = escrowed
    · simp [isIt] at merged
    · simp [isIt] at merged
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by
    intro occurrence reason acknowledged
    by_cases isIt : occurrence = escrowed
    · simp [isIt] at acknowledged
    · simp [isIt] at acknowledged

open Classical in
/--
What each session holds, before (`false`) and after (`true`) the receive.

One function rather than two inline lambdas, so that "off `wire` the two worlds
agree" is a lemma with clean types rather than a tactic block fighting the
classical decidability instance.

Only `wire` holds anything. That matters for the step's scope proof: a world
whose every session changed would not have touched one fragment.
-/
noncomputable def ledgerAt (settled : Bool) (session : serverTopology.ChannelId ()) :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) :=
  if session = wire then (if settled then settledLedger else pendingLedger)
  else EscrowLedger.empty

/-- On `wire`, it is the ledger the step is about. -/
@[simp] theorem ledgerAt_wire (settled : Bool) :
    ledgerAt settled wire = if settled then settledLedger else pendingLedger := by
  simp [ledgerAt]

/-- Off `wire`, the two worlds hold the same thing — which is the scope claim. -/
theorem ledgerAt_off_wire {session : serverTopology.ChannelId ()}
    (notWire : session ≠ wire) : ledgerAt false session = ledgerAt true session := by
  simp [ledgerAt, notWire]

/-- And off the wire it is the empty ledger, which is what `quiet` holds. -/
theorem ledgerAt_off_wire_empty {session : serverTopology.ChannelId ()}
    (notWire : session ≠ wire) (settled : Bool) :
    ledgerAt settled session = EscrowLedger.empty := by
  simp [ledgerAt, notWire]

open Classical in
/--
The receiver's cursor on each session, before and after.

A delivery advances the cursor of the session it was delivered on and no other,
which is what makes `Delivers.scope` a real constraint rather than a formality.
-/
noncomputable def cursorAt (advanced : Bool) (session : serverTopology.ChannelId ()) :
    ChannelSession :=
  if session = wire then
    { quiet.sessions () wire with
        delivered := (quiet.sessions () wire).delivered + (if advanced then 1 else 0) }
  else quiet.sessions () session

theorem cursorAt_off_wire {session : serverTopology.ChannelId ()} (notWire : session ≠ wire)
    (advanced : Bool) : cursorAt advanced session = quiet.sessions () session := by
  simp [cursorAt, notWire]

/-- The world before the receive. -/
noncomputable def beforeReceive : ServerWorld :=
  { quiet with
      inFlight := fun _ => ledgerAt false
      sessions := fun _ => cursorAt false
      pending := [Observation.beep] }

/-- And after it: the escrow settled, and the receiver's cursor moved by one. -/
noncomputable def afterReceive : ServerWorld :=
  { quiet with
      inFlight := fun _ => ledgerAt true
      sessions := fun _ => cursorAt true
      pending := [Observation.beep] }

/-- What each world holds on `wire`. -/
@[simp] theorem beforeReceive_wire :
    beforeReceive.inFlight () wire = pendingLedger := by
  simp [beforeReceive]

@[simp] theorem afterReceive_wire :
    afterReceive.inFlight () wire = settledLedger := by
  simp [afterReceive]

/-- And off it, the two agree. -/
theorem worlds_agree_off_wire {session : serverTopology.ChannelId ()}
    (notWire : session ≠ wire) :
    beforeReceive.inFlight () session = afterReceive.inFlight () session :=
  ledgerAt_off_wire notWire

/-- And what `settledLedger` says about the occurrence. -/
@[simp] theorem settled_resolution :
    settledLedger.resolution escrowed = some .received := by
  simp [settledLedger]

@[simp] theorem pending_resolution :
    pendingLedger.resolution escrowed = none := rfl

open Classical in
/--
And what it says about every *other* occurrence: nothing.

`ResolvesNothingElse` is the field that stops a step resolving an occurrence it
never mentioned — see `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.87 and the drop
in `Tests/Process/RerouteFixtures.lean` that the field now refuses. Here it is
the honest reading of a ledger that resolves exactly one thing.
-/
theorem settled_resolution_off {occurrence : EdgeOccurrence serverTopology
    World.serverMessage ()} (notIt : occurrence ≠ escrowed) :
    settledLedger.resolution occurrence = none := by
  show (if occurrence = escrowed then some ChannelResolution.received else none) = none
  rw [if_neg notIt]

/-- A receive resolves the occurrence it received, and nothing else. -/
theorem receive_resolves_nothing_else :
    ResolvesNothingElse pendingLedger settledLedger escrowed :=
  fun _ notIt => settled_resolution_off notIt

/-- And a send resolves nothing at all: both ledgers are silent. -/
theorem send_resolves_nothing : ResolvesNothing EscrowLedger.empty pendingLedger :=
  fun _ => rfl

/-! ## The step -/

/--
**A receive resolves the escrow and advances the receiver's cursor.**

Every field of `Delivers` at a concrete pair of worlds: the occurrence was
outstanding, it is now `received` and nothing else, the ledger only moved
forward, the cursor advanced by exactly one, the session is still open, and the
step's scope is this session's escrow and this session's cursor.

The cursor is here because it had to be. Before `Delivers` existed, `receive`
was a `ResolvesEscrow` whose scope named the escrow alone — so no constructor in
the family named `.session` at all, and by `touchesOnly` a session's cursor and
status could never move in any program. `ChannelSession.delivered` was provably
constant.
-/
theorem receiving_resolves_the_escrow :
    serverPlan.Delivers beforeReceive afterReceive () wire escrowed where
  contractual := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [beforeReceive_wire]
      exact ⟨List.mem_cons_self, rfl⟩
    · simp [beforeReceive, cursorAt, Grass.Process.Tests.World.quiet]
    · simp [beforeReceive, afterReceive, cursorAt]
  onItsSession := rfl
  wasOutstanding := by
    rw [beforeReceive_wire]
    exact ⟨List.mem_cons_self, rfl⟩
  nowResolved := by
    rw [afterReceive_wire]
    exact settled_resolution
  resolvesNothingElse := by
    rw [beforeReceive_wire, afterReceive_wire]
    exact receive_resolves_nothing_else
  createsNothing := by
    show CreatesNothing (beforeReceive.inFlight () wire) (afterReceive.inFlight () wire)
    rw [beforeReceive_wire, afterReceive_wire]
    rfl
  requestsNothing := by
    show RequestsNothing (beforeReceive.inFlight () wire) (afterReceive.inFlight () wire)
    rw [beforeReceive_wire, afterReceive_wire]
    exact fun _ => rfl
  ledgerExtends := by
    rw [beforeReceive_wire, afterReceive_wire]
    exact
      { createdPrefix := List.prefix_refl _
        resolutionPermanent := by
          intro occurrence resolution ended
          exact absurd ended (by simp [pendingLedger])
        cancelRequestMonotone := by
          intro occurrence requested
          exact absurd requested (by simp [pendingLedger]) }
  cursorAdvances := by simp [beforeReceive, afterReceive, cursorAt]
  statusUnchanged := by simp [beforeReceive, afterReceive, cursorAt]
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := by
        intro isWire
        subst isWire
        exact outside (Or.inl rfl)
      exact worlds_agree_off_wire notWire
    | session edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := by
        intro isWire
        subst isWire
        exact outside (Or.inr rfl)
      show cursorAt false session = cursorAt true session
      rw [cursorAt_off_wire notWire, cursorAt_off_wire notWire]
    | _ => rfl

/--
**And it cannot happen twice.**

The affine half of §3's resolve token, at the step — now with a second,
independent reason. `Delivers` demands the occurrence was outstanding *before*,
so a second receive from the world the first produced is unconstructible on the
escrow; and its cursor law demands `delivered = delivered + 1`, which is
unsatisfiable at a single world whatever the escrow says.

Proved from the cursor, because that is the half `Delivers` added and it is
worth checking that the addition is load-bearing.
-/
theorem cannot_receive_twice
    (again : serverPlan.Delivers afterReceive afterReceive () wire escrowed) : False := by
  have counted := again.cursorAdvances
  omega

/--
**The observation trace did not move.**

Read straight out of the step's own scope proof. A weave invariant over
observations frames past this step without knowing what the step was, which is
what `docs/PROCESS.md` §8's `Disjoint (TransitionScope step) Scope` buys.
-/
theorem observations_did_not_move :
    beforeReceive.observations = afterReceive.observations :=
  receiving_resolves_the_escrow.scope .observations (by simp)

/-- As did every instance slot, which the same proof gives. -/
theorem instances_did_not_move (kind : serverTopology.ProcessKind)
    (slot : serverTopology.InstanceId kind) :
    beforeReceive.instances kind slot = afterReceive.instances kind slot :=
  receiving_resolves_the_escrow.scope (.instanceState kind slot) (by simp)

/-! ## The step as a member of the family -/

/-- The receive, as a `NetworkTransition`. -/
def receiveStep : serverPlan.NetworkTransition beforeReceive afterReceive :=
  .receive () wire escrowed receiving_resolves_the_escrow

/--
**Its scope is one fragment, and it respected it.**

`touchesOnly` is proved once over the whole family, so this is not a fact about
this step in particular — but reading it back at a concrete step is what shows
the general theorem is about something. `docs/PROCESS.md` §8's
`Disjoint (TransitionScope step) Scope` now has a `TransitionScope` to be
disjoint from.
-/
theorem receive_touches_only_its_session :
    serverPlan.TouchesOnly beforeReceive afterReceive receiveStep.scope :=
  receiveStep.touchesOnly

/--
And that scope is the one session's escrow and the one session's cursor,
nothing more.
-/
theorem receive_scope_is_the_session (fragment : NetworkFragment serverTopology) :
    receiveStep.scope fragment ↔
      (fragment = .escrow () wire ∨ fragment = .session () wire) := Iff.rfl

/--
**The receiver's cursor really moved.**

The anti-vacuity check on `Delivers`. Before it existed no constructor named
`.session` in its scope, so `ChannelSession.delivered` was provably constant in
every program and a weave mixin about a session cursor framed past every step.
-/
theorem the_cursor_advanced :
    (afterReceive.sessions () wire).delivered =
      (beforeReceive.sessions () wire).delivered + 1 :=
  receiving_resolves_the_escrow.cursorAdvances

/-- **And `.session` is a fragment some step of some program actually declares.** -/
theorem the_receive_touches_its_session : receiveStep.scope (.session () wire) :=
  Or.inr rfl

/-- But only its own: another session's cursor is untouched. -/
theorem other_cursors_did_not_move {session : serverTopology.ChannelId ()}
    (notWire : session ≠ wire) :
    beforeReceive.sessions () session = afterReceive.sessions () session :=
  receiveStep.touchesOnly (.session () session) (by
    rintro (isEscrow | isSession)
    · exact absurd isEscrow (by simp)
    · injection isSession with _ sameSession
      exact notWire sameSession)

/-- A receive allocates nothing, definitionally. -/
theorem receive_allocates_nothing :
    receiveStep.allocatedNominals = Allocation.empty := rfl

/--
**So it is a step, and the history did not move.**

`NetworkStep` bundles the transition with `docs/PROCESS.md` §3's freshness law.
For a non-allocating transition the law is vacuous and the history equation says
the history is unchanged, which `nonallocating_preserves_history` reads back.
-/
def receiveAsStep : serverPlan.NetworkStep beforeReceive afterReceive where
  transition := receiveStep
  admissible := by
    intro nominal allocated
    have nothing : nominal ∈ (Allocation.empty : Allocation serverTopology.Carrier).entries :=
      receive_allocates_nothing ▸ allocated
    exact absurd nothing (fun inEmpty => List.not_mem_nil inEmpty)
  historyExact := (NominalHistory.extend_empty _ _).symm

theorem history_did_not_move :
    afterReceive.usedNominals = beforeReceive.usedNominals :=
  receiveAsStep.nonallocating_preserves_history rfl

/-! ## And a session that has been shut -/

open Classical in
/--
The same world with the wire session closed.

**Not reachable by `channelClose` from any world**, and an earlier version of
this docstring said it was. `ClosesSession.nowResolved` requires the occurrence
to be resolved `.channelClosed` afterwards, and this world keeps
`beforeReceive`'s ledgers, in which nothing is resolved at all — so no
`ClosesSession` can produce it, on any session, from any before-world. A reviewer
checked.

It is a *manufactured* world, and what it is for is stated exactly:
`nothing_can_be_sent_on_the_shut_wire` below is a fact about a world with a
closed session, and this is the smallest such world. What the corpus does not
have is a world with a closed session that a run reaches, which needs a
`ClosesSession` witness — `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.79.
-/
noncomputable def afterClose : ServerWorld :=
  { beforeReceive with
      sessions := fun _ session =>
        if session = wire then { cursorAt false wire with status := .closed }
        else cursorAt false session }

/-- It really is shut. -/
theorem the_wire_is_shut : (afterClose.sessions () wire).status ≠ .open := by
  simp [afterClose]

/--
**And nothing can be sent on it.**

`ProcessPlan.no_send_on_a_closed_session` at a concrete plan and a concrete
world. Three fields compose to get here: `sendOnOpenSession` makes the session
law a demand, `sessionOpenIsRecorded` says the demanded assertion *is* the
recorded status, and `ClosesSession` is what can put a status there.

Each of the three was added because the previous one was not enough on its own,
and none of them was found by reading the module that owns it.

The composition is real and the world it is stated at is not reachable; see
`afterClose`.
-/
theorem nothing_can_be_sent_on_the_shut_wire
    {message : serverPlan.message ()}
    {occurrence : serverTopology.ChannelOccurrence () message}
    {after : serverPlan.LogicalProcessNetwork}
    (onWire : occurrence.1 = wire)
    (sent : (serverPlan.steps ()).Send message occurrence afterClose after) : False :=
  serverPlan.no_send_on_a_closed_session sent (by rw [onWire]; exact the_wire_is_shut)

/-! ## A send that the receive can follow -/

/--
The world one send reaches: the occurrence escrowed on the wire, nothing else
moved.

`beforeReceive` is not this world — it also holds a pending `beep`, which a send
does not produce — and that difference is the finding this section exists for.
A reviewer proved that **no** `SendsEscrow` of this plan could reach
`beforeReceive`, so the corpus exercised a send and a receive that had nothing to
do with each other. The chain below is the composition.
-/
noncomputable def sent : ServerWorld :=
  { quiet with inFlight := fun _ => ledgerAt false }

@[simp] theorem sent_wire : sent.inFlight () wire = pendingLedger := by simp [sent]

/-- Nothing was in flight before it. -/
theorem quiet_holds_nothing (session : serverTopology.ChannelId ()) :
    quiet.inFlight () session = EscrowLedger.empty := rfl

/--
**A send: the corpus's first `SendsEscrow`.**

`contractual` is the plan's own send relation, which is what makes this a send of
*this* program rather than a shape that happens to typecheck — the same field
`Delivers` waited four review rounds for.
-/
theorem the_send : serverPlan.SendsEscrow quiet sent () payload occurrenceOf where
  contractual :=
    ⟨rfl, rfl, by rw [quiet_holds_nothing]; exact List.not_mem_nil,
      by rw [sent_wire]; exact ⟨List.mem_cons_self, rfl⟩⟩
  wasFresh := by
    show escrowed ∉ (quiet.inFlight () wire).created
    rw [quiet_holds_nothing]
    exact List.not_mem_nil
  nowEscrowed := by
    show (sent.inFlight () wire).Outstanding escrowed
    rw [sent_wire]
    exact ⟨List.mem_cons_self, rfl⟩
  resolvesNothing := by
    show ResolvesNothing (quiet.inFlight () wire) (sent.inFlight () wire)
    rw [quiet_holds_nothing, sent_wire]
    exact send_resolves_nothing
  requestsNothing := by
    show RequestsNothing (quiet.inFlight () wire) (sent.inFlight () wire)
    rw [quiet_holds_nothing, sent_wire]
    exact fun _ => rfl
  createsOnlyTheMessage := by
    intro other held _
    show other = escrowed
    have onWire : other ∈ (sent.inFlight () wire).created := held
    rw [sent_wire] at onWire
    have inList : other ∈ [escrowed] := onWire
    exact List.mem_singleton.mp inList
  ledgerExtends := by
    show LedgerExtends (quiet.inFlight () wire) (sent.inFlight () wire)
    rw [quiet_holds_nothing, sent_wire]
    exact
      { createdPrefix := List.nil_prefix
        resolutionPermanent := by
          intro occurrence resolution ended
          exact absurd ended (by simp [EscrowLedger.empty])
        cancelRequestMonotone := by
          intro occurrence requested
          exact absurd requested (by simp [EscrowLedger.empty]) }
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := by
        intro isWire
        subst isWire
        exact outside rfl
      show quiet.inFlight () session = sent.inFlight () session
      rw [show sent.inFlight () session = ledgerAt false session from rfl,
        ledgerAt_off_wire_empty notWire]
      rfl
    | _ => rfl

/-- **And it puts the message in flight**, which is `ProcessPlan`'s two tie
fields composed at a step that actually happened. -/
theorem the_send_puts_it_in_flight :
    (sent.inFlight () occurrenceOf.1).Outstanding escrowed :=
  serverPlan.send_puts_it_in_flight (carried := payload) the_send.contractual trivial

/--
**And the receive follows it.**

The pair, at the two worlds a run of this plan actually visits. `Delivers`
requires the receiver's cursor to be at zero, which is `sent`'s — nothing has
been delivered on the wire — so this is the receive the send set up rather than a
receive at a world nobody arrived at.
-/
noncomputable def received : ServerWorld :=
  { quiet with inFlight := fun _ => ledgerAt true, sessions := fun _ => cursorAt true }

@[simp] theorem received_wire : received.inFlight () wire = settledLedger := by simp [received]

theorem the_receive_after_the_send :
    serverPlan.Delivers sent received () wire escrowed where
  contractual := by
    refine ⟨rfl, ?_, rfl, ?_⟩
    · rw [sent_wire]
      exact ⟨List.mem_cons_self, rfl⟩
    · simp [sent, received, cursorAt, Grass.Process.Tests.World.quiet]
  onItsSession := rfl
  wasOutstanding := by
    rw [sent_wire]
    exact ⟨List.mem_cons_self, rfl⟩
  resolvesNothingElse := by
    rw [sent_wire, received_wire]
    exact receive_resolves_nothing_else
  createsNothing := by
    show CreatesNothing (sent.inFlight () wire) (received.inFlight () wire)
    rw [sent_wire, received_wire]
    rfl
  requestsNothing := by
    show RequestsNothing (sent.inFlight () wire) (received.inFlight () wire)
    rw [sent_wire, received_wire]
    exact fun _ => rfl
  nowResolved := by
    rw [received_wire]
    exact settled_resolution
  ledgerExtends := by
    rw [sent_wire, received_wire]
    exact
      { createdPrefix := List.prefix_refl _
        resolutionPermanent := by
          intro occurrence resolution ended
          exact absurd ended (by simp [pendingLedger])
        cancelRequestMonotone := by
          intro occurrence requested
          exact absurd requested (by simp [pendingLedger]) }
  cursorAdvances := by simp [sent, received, cursorAt, Grass.Process.Tests.World.quiet]
  statusUnchanged := by simp [sent, received, cursorAt]
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := by
        intro isWire
        subst isWire
        exact outside (Or.inl rfl)
      show sent.inFlight () session = received.inFlight () session
      rw [show sent.inFlight () session = ledgerAt false session from rfl,
        show received.inFlight () session = ledgerAt true session from rfl,
        ledgerAt_off_wire notWire]
    | session edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := by
        intro isWire
        subst isWire
        exact outside (Or.inr rfl)
      show sent.sessions () session = received.sessions () session
      rw [show received.sessions () session = cursorAt true session from rfl,
        cursorAt_off_wire notWire]
      rfl
    | _ => rfl


end Grass.Process.Tests.Transition
