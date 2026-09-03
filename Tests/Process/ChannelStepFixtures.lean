import Tests.Process.TransitionFixtures

/-!
# The channel constructors nothing had ever built

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.79: of `NetworkTransition`'s twelve
channel constructors, only `.receive` was ever built in this corpus.
`SendsEscrow` was the first repair — `Tests/Process/TransitionFixtures.lean`'s
`the_send` — and this file is the rest of the sweep: a close, a channel death, a
cancellation request and a drop, each at the world the send reaches.

Why it matters beyond coverage. A reviewer proved that `Delivers` carried
`onItsSession` — the occurrence's own `ChannelId` is the session the step is
about — and that its five siblings did not, so one occurrence could be resolved
once on each of two sessions and neither ledger would notice.
`EscrowLedger.atMostOneRecordedEnding` is a fact about one ledger; §3's affine
resolve token is not. The five fields went in and **not one proof broke**, which
is this milestone's seven-for-seven signal that nothing inhabits the structures.
These are the witnesses, and `a_close_on_the_wrong_session_is_refused` is the
refusal that field now supplies.

## And the eleventh

`Reroutes` was held back here on the grounds that it needed a change to the
fixture world. It did not: a `ChannelId` carries an epoch, so a second session on
this edge is `wire` with a later one. `Tests/Process/RerouteFixtures.lean` is the
witness, and the mistaken argument is recorded in §10.79 beside the others this
milestone made from reading rather than building.
-/

namespace Grass.Process.Tests.ChannelStep

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld quiet)
open Grass.Process.Tests.Channel (wire)
open Grass.Process.Tests.Transition
  (serverPlan payload occurrenceOf escrowed pendingLedger sent sent_wire
   ledgerAt ledgerAt_off_wire_empty cursorAt cursorAt_off_wire)

/-! ## Three ways for the wire's one occurrence to end -/

open Classical in
/-- The ledger with the occurrence resolved as the channel closing. -/
noncomputable def closedLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun occurrence => if occurrence = escrowed then some .channelClosed else none
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
/-- The ledger with it resolved as the channel dying. -/
noncomputable def diedLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun occurrence => if occurrence = escrowed then some .channelDied else none
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
/-- The ledger with it dropped by an explicitly modelled disposition. -/
noncomputable def droppedLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun occurrence => if occurrence = escrowed then some .dropped else none
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
/-- And the ledger with a cancellation requested against it, still unresolved. -/
noncomputable def requestedLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun _ => none
  noFabrication := by simp
  coalesceCarrierLater := by simp
  cancelRequested := fun occurrence => if occurrence = escrowed then true else false
  acknowledgedWasRequested := by simp

/-! ## Four worlds the send's world can reach -/

open Classical in
/-- The wire closed, its occurrence resolved by the closing. -/
noncomputable def afterClosing : ServerWorld :=
  { sent with
      inFlight := fun _ session => if session = wire then closedLedger else EscrowLedger.empty
      sessions := fun _ session =>
        if session = wire then { cursorAt false wire with status := .closed }
        else cursorAt false session }

open Classical in
/-- The wire dead, likewise. -/
noncomputable def afterDying : ServerWorld :=
  { sent with
      inFlight := fun _ session => if session = wire then diedLedger else EscrowLedger.empty
      sessions := fun _ session =>
        if session = wire then { cursorAt false wire with status := .died }
        else cursorAt false session }

open Classical in
/-- A cancellation recorded against the occurrence. -/
noncomputable def afterRequesting : ServerWorld :=
  { sent with
      inFlight := fun _ session =>
        if session = wire then requestedLedger else EscrowLedger.empty }

open Classical in
/-- And the occurrence dropped. -/
noncomputable def afterDropping : ServerWorld :=
  { sent with
      inFlight := fun _ session => if session = wire then droppedLedger else EscrowLedger.empty }

@[simp] theorem afterClosing_wire : afterClosing.inFlight () wire = closedLedger := by
  simp [afterClosing]

@[simp] theorem afterDying_wire : afterDying.inFlight () wire = diedLedger := by
  simp [afterDying]

@[simp] theorem afterRequesting_wire : afterRequesting.inFlight () wire = requestedLedger := by
  simp [afterRequesting]

@[simp] theorem afterDropping_wire : afterDropping.inFlight () wire = droppedLedger := by
  simp [afterDropping]

open Classical in
theorem afterClosing_off {session : serverTopology.ChannelId ()} (notWire : session ≠ wire) :
    afterClosing.inFlight () session = EscrowLedger.empty := by
  show (if session = wire then closedLedger else EscrowLedger.empty) = EscrowLedger.empty
  rw [if_neg notWire]

open Classical in
theorem afterClosing_sessions_off {session : serverTopology.ChannelId ()}
    (notWire : session ≠ wire) : afterClosing.sessions () session = cursorAt false session := by
  show (if session = wire then { cursorAt false wire with status := .closed }
    else cursorAt false session) = cursorAt false session
  rw [if_neg notWire]

open Classical in
theorem afterDying_off {session : serverTopology.ChannelId ()} (notWire : session ≠ wire) :
    afterDying.inFlight () session = EscrowLedger.empty := by
  show (if session = wire then diedLedger else EscrowLedger.empty) = EscrowLedger.empty
  rw [if_neg notWire]

open Classical in
theorem afterDying_sessions_off {session : serverTopology.ChannelId ()}
    (notWire : session ≠ wire) : afterDying.sessions () session = cursorAt false session := by
  show (if session = wire then { cursorAt false wire with status := .died }
    else cursorAt false session) = cursorAt false session
  rw [if_neg notWire]

open Classical in
theorem afterRequesting_off {session : serverTopology.ChannelId ()} (notWire : session ≠ wire) :
    afterRequesting.inFlight () session = EscrowLedger.empty := by
  show (if session = wire then requestedLedger else EscrowLedger.empty) = EscrowLedger.empty
  rw [if_neg notWire]

open Classical in
theorem afterDropping_off {session : serverTopology.ChannelId ()} (notWire : session ≠ wire) :
    afterDropping.inFlight () session = EscrowLedger.empty := by
  show (if session = wire then droppedLedger else EscrowLedger.empty) = EscrowLedger.empty
  rw [if_neg notWire]

/-! ## What each ledger says about the occurrence -/

open Classical in
theorem closedLedger_resolution :
    closedLedger.resolution escrowed = some .channelClosed := by
  show (if escrowed = escrowed then some ChannelResolution.channelClosed else none)
    = some ChannelResolution.channelClosed
  rw [if_pos rfl]

open Classical in
theorem diedLedger_resolution :
    diedLedger.resolution escrowed = some .channelDied := by
  show (if escrowed = escrowed then some ChannelResolution.channelDied else none)
    = some ChannelResolution.channelDied
  rw [if_pos rfl]

open Classical in
theorem droppedLedger_resolution :
    droppedLedger.resolution escrowed = some .dropped := by
  show (if escrowed = escrowed then some ChannelResolution.dropped else none)
    = some ChannelResolution.dropped
  rw [if_pos rfl]

open Classical in
theorem requestedLedger_requested :
    requestedLedger.cancelRequested escrowed = true := by
  show (if escrowed = escrowed then true else false) = true
  rw [if_pos rfl]

/-! ## The ledger moved forward each time -/

/-- Every one of these steps extends the wire's ledger: nothing erased, no
resolution rewritten, no cancellation un-requested. -/
theorem pending_extends_to
    (later : EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()))
    (sameCreated : later.created = [escrowed])
    (noCancels : ∀ occurrence, pendingLedger.cancelRequested occurrence = true →
      later.cancelRequested occurrence = true) :
    LedgerExtends pendingLedger later where
  createdPrefix := by rw [sameCreated]; exact List.prefix_refl _
  resolutionPermanent := by
    intro occurrence resolution ended
    exact absurd ended (by simp [pendingLedger])
  cancelRequestMonotone := noCancels

/-! ## Off the wire, nothing moved -/

/-- The four after-worlds agree with `sent` on every session but the wire. -/
theorem off_wire_ledgers {session : serverTopology.ChannelId ()} (notWire : session ≠ wire)
    (world : ServerWorld)
    (isEmpty : world.inFlight () session = EscrowLedger.empty) :
    sent.inFlight () session = world.inFlight () session := by
  rw [isEmpty, show sent.inFlight () session = ledgerAt false session from rfl,
    ledgerAt_off_wire_empty notWire]

open Classical in
/--
And what each of them says about every *other* occurrence: nothing.

`ResolvesNothingElse` is the field local construction forced -- see
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.87 and the stranding drop in
`Tests/Process/RerouteFixtures.lean` it refuses. Each of these ledgers resolves
exactly the one occurrence its step is about, which is what makes them honest
witnesses of it rather than ledgers that happen to satisfy it.
-/
theorem closedLedger_resolves_nothing_else :
    ResolvesNothingElse pendingLedger closedLedger escrowed := by
  intro occurrence notIt
  show (if occurrence = escrowed then some ChannelResolution.channelClosed else none) = none
  rw [if_neg notIt]

open Classical in
theorem diedLedger_resolves_nothing_else :
    ResolvesNothingElse pendingLedger diedLedger escrowed := by
  intro occurrence notIt
  show (if occurrence = escrowed then some ChannelResolution.channelDied else none) = none
  rw [if_neg notIt]

open Classical in
theorem droppedLedger_resolves_nothing_else :
    ResolvesNothingElse pendingLedger droppedLedger escrowed := by
  intro occurrence notIt
  show (if occurrence = escrowed then some ChannelResolution.dropped else none) = none
  rw [if_neg notIt]

open Classical in
/-- And it requests the cancellation of that occurrence and no other. -/
theorem requestedLedger_requests_nothing_else :
    RequestsNothingElse pendingLedger requestedLedger escrowed := by
  intro other notIt
  show (if other = escrowed then true else false) = false
  rw [if_neg notIt]

/-- A cancellation request resolves nothing at all: it records and does not end. -/
theorem requestedLedger_resolves_nothing :
    ResolvesNothing pendingLedger requestedLedger :=
  fun _ => rfl

/-- At `sent` the wire holds exactly one occurrence in flight, which is what a
close or a death has to end all of. -/
theorem only_the_one_is_outstanding {occurrence : EdgeOccurrence serverTopology
    World.serverMessage ()} (outstanding : (sent.inFlight () wire).Outstanding occurrence) :
    occurrence = escrowed := by
  rw [sent_wire] at outstanding
  have held : occurrence ∈ [escrowed] := outstanding.1
  simpa using held

/-! ## The four steps -/

/--
**A close: the corpus's first `ClosesSession`.**

`SessionStatus.closed` was producible by nothing until this constructor existed,
and until this fixture nothing produced it. `onItsSession` is the field a
reviewer's two-step attack made necessary; `a_close_on_the_wrong_session_is_refused`
below is what it now refuses.
-/
theorem the_close : serverPlan.ClosesSession sent afterClosing () wire escrowed where
  onItsSession := rfl
  wasOutstanding := by rw [sent_wire]; exact ⟨List.mem_cons_self, rfl⟩
  closesEverything := by
    intro other _ outstanding
    rw [only_the_one_is_outstanding outstanding, afterClosing_wire]
    exact closedLedger_resolution
  resolvesOnlyAs := by
    rw [sent_wire, afterClosing_wire]
    exact closedLedger_resolves_nothing_else.resolvesOnlyAs closedLedger_resolution
  createsNothing := by
    show CreatesNothing (sent.inFlight () wire) (afterClosing.inFlight () wire)
    rw [sent_wire, afterClosing_wire]
    rfl
  requestsNothing := by
    show RequestsNothing (sent.inFlight () wire) (afterClosing.inFlight () wire)
    rw [sent_wire, afterClosing_wire]
    exact fun _ => rfl
  ledgerExtends := by
    rw [sent_wire, afterClosing_wire]
    exact pending_extends_to closedLedger rfl (by simp [pendingLedger])
  wasOpen := rfl
  nowClosed := by simp [afterClosing]
  cursorUnchanged := by simp [afterClosing, sent, cursorAt, Grass.Process.Tests.World.quiet]
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := fun isWire => outside (Or.inl (by rw [isWire]))
      exact off_wire_ledgers notWire afterClosing (afterClosing_off notWire)
    | session edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := fun isWire => outside (Or.inr (by rw [isWire]))
      show sent.sessions () session = afterClosing.sessions () session
      rw [afterClosing_sessions_off notWire, cursorAt_off_wire notWire]
      rfl
    | _ => rfl

/-- **A channel death**, the sibling `ClosesSession` was split from — and the
status it produces is not a closure, which is why `KillsSession` exists. -/
theorem the_death : serverPlan.KillsSession sent afterDying () wire escrowed where
  onItsSession := rfl
  wasOutstanding := by rw [sent_wire]; exact ⟨List.mem_cons_self, rfl⟩
  killsEverything := by
    intro other _ outstanding
    rw [only_the_one_is_outstanding outstanding, afterDying_wire]
    exact diedLedger_resolution
  resolvesOnlyAs := by
    rw [sent_wire, afterDying_wire]
    exact diedLedger_resolves_nothing_else.resolvesOnlyAs diedLedger_resolution
  createsNothing := by
    show CreatesNothing (sent.inFlight () wire) (afterDying.inFlight () wire)
    rw [sent_wire, afterDying_wire]
    rfl
  requestsNothing := by
    show RequestsNothing (sent.inFlight () wire) (afterDying.inFlight () wire)
    rw [sent_wire, afterDying_wire]
    exact fun _ => rfl
  ledgerExtends := by
    rw [sent_wire, afterDying_wire]
    exact pending_extends_to diedLedger rfl (by simp [pendingLedger])
  wasOpen := rfl
  nowDied := by simp [afterDying]
  cursorUnchanged := by simp [afterDying, sent, cursorAt, Grass.Process.Tests.World.quiet]
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := fun isWire => outside (Or.inl (by rw [isWire]))
      exact off_wire_ledgers notWire afterDying (afterDying_off notWire)
    | session edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := fun isWire => outside (Or.inr (by rw [isWire]))
      show sent.sessions () session = afterDying.sessions () session
      rw [afterDying_sessions_off notWire, cursorAt_off_wire notWire]
      rfl
    | _ => rfl

/-! ## A death that is a death -/

/-- The wire's sender, stopped. -/
def deadListener : ProcessInstance serverTopology :=
  { World.rootListener with lifecycle := .died .supervised }

theorem deadListener_is_not_live : ¬ deadListener.Live := by
  intro live
  cases live

/-- And it died, supervised, at the generation the wire's sender names — the three
things `ResolvesEscrow.endpointDeathIsEarned` asks. §10.117. -/
theorem deadListener_died :
    deadListener.ref.generation = wire.sender.generation ∧
      deadListener.lifecycle = .died .supervised :=
  ⟨rfl, rfl⟩

/-- The sent world, with the sender present and dead. -/
noncomputable def sentWithDeadSender : ServerWorld :=
  { sent with
      instances := fun kind _ =>
        match kind with
        | .listener => some deadListener
        | .connection => none }

theorem sentWithDeadSender_wire :
    sentWithDeadSender.inFlight () wire = pendingLedger := sent_wire

open Classical in
/-- The ledger with the occurrence resolved by its sender's death. -/
noncomputable def senderDiedLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun occurrence =>
    if occurrence = escrowed then some (.senderDied .supervised) else none
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
theorem senderDiedLedger_resolution :
    senderDiedLedger.resolution escrowed = some (.senderDied .supervised) := by
  show (if escrowed = escrowed then some (ChannelResolution.senderDied .supervised) else none)
    = some (ChannelResolution.senderDied .supervised)
  rw [if_pos rfl]

open Classical in
theorem senderDiedLedger_resolves_nothing_else :
    ResolvesNothingElse pendingLedger senderDiedLedger escrowed := by
  intro occurrence notIt
  show (if occurrence = escrowed then some (ChannelResolution.senderDied .supervised) else none)
    = none
  rw [if_neg notIt]

open Classical in
/-- The world after the sender's death. -/
noncomputable def afterSenderDeath : ServerWorld :=
  { sentWithDeadSender with
      inFlight := fun _ session => if session = wire then senderDiedLedger else EscrowLedger.empty }

open Classical in
theorem afterSenderDeath_wire : afterSenderDeath.inFlight () wire = senderDiedLedger := by
  show (if wire = wire then senderDiedLedger else EscrowLedger.empty) = senderDiedLedger
  rw [if_pos rfl]

open Classical in
theorem afterSenderDeath_off {session : serverTopology.ChannelId ()} (notWire : session ≠ wire) :
    afterSenderDeath.inFlight () session = EscrowLedger.empty := by
  show (if session = wire then senderDiedLedger else EscrowLedger.empty) = EscrowLedger.empty
  rw [if_neg notWire]

/--
**A sender's death, at a world where the sender is present and dead.**

The witness `ResolvesEscrow.endpointDeathIsEarned` needed. Before that field,
`senderDeath` mentioned no process at all: a reviewer ran two of these from
`quiet` and read back a session whose ledger records both endpoints dead in a
world where neither has ever existed, with the session still open.
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.114.

`a_death_needs_a_dead_endpoint` is the refusal; this is the half §10.110 says a
new field also needs, so the field is not one that forbids everything.
-/
theorem the_sender_death :
    serverPlan.ResolvesEscrow sentWithDeadSender afterSenderDeath () wire escrowed
      (.senderDied .supervised) where
  onItsSession := rfl
  wasOutstanding := by
    rw [sentWithDeadSender_wire]
    exact ⟨List.mem_cons_self, rfl⟩
  nowResolved := by rw [afterSenderDeath_wire]; exact senderDiedLedger_resolution
  resolvesNothingElse := by
    rw [sentWithDeadSender_wire, afterSenderDeath_wire]
    exact senderDiedLedger_resolves_nothing_else
  requestsNothing := by
    show RequestsNothing (sentWithDeadSender.inFlight () wire) (afterSenderDeath.inFlight () wire)
    rw [sentWithDeadSender_wire, afterSenderDeath_wire]
    exact fun _ => rfl
  ledgerExtends := by
    rw [sentWithDeadSender_wire, afterSenderDeath_wire]
    exact pending_extends_to senderDiedLedger rfl (by simp [pendingLedger])
  createsOnlyTheCarrier := by
    intro other held fresh
    refine absurd ?_ fresh
    show other ∈ (sentWithDeadSender.inFlight () wire).created
    rw [sentWithDeadSender_wire]
    have inList : other ∈ (afterSenderDeath.inFlight () wire).created := held
    rw [afterSenderDeath_wire] at inList
    exact inList
  carrierOnItsSession := by intro carrier isCoalesce; cases isCoalesce
  carrierIsOutstanding := by intro carrier isCoalesce; cases isCoalesce
  carrierCarriesTheMessage := by intro carrier isCoalesce; cases isCoalesce
  endpointDeathIsEarned := by
    constructor
    · intro reason isDeath
      cases isDeath
      exact ⟨deadListener, rfl, deadListener_died.1, deadListener_died.2⟩
    · intro reason isDeath
      cases isDeath
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := fun isWire => outside (by rw [isWire])
      show ledgerAt false session = afterSenderDeath.inFlight () session
      rw [ledgerAt_off_wire_empty notWire, afterSenderDeath_off notWire]
    | _ => rfl

/--
**And a death with no dead endpoint is refused.**

The other half. `senderDeath`, `receiverDeath` and `drop` were the same relation
up to the tag written into the ledger, which made decision 129's stored
classification unreadable off network state. §10.114.
-/
theorem a_death_needs_a_dead_endpoint
    {before after : ServerWorld} {reason : ProcessDeathReason}
    (nobodyThere : ∀ (kind : serverPlan.topology.ProcessKind) slot,
      before.instances kind slot = none)
    (died : serverPlan.ResolvesEscrow before after () wire escrowed (.senderDied reason)) :
    False := by
  obtain ⟨incarnation, present, _⟩ := died.endpointDeathIsEarned.1 reason rfl
  exact absurd (present.symm.trans (nobodyThere _ _)) (by intro equal; cases equal)

/-- The wire's receiver, stopped, at the generation the wire names. -/
def deadConnection : ProcessInstance serverTopology where
  kind := .connection
  ref := connectionSeven 0
  parentage := .attached .listener Instances.listenerZero
  request := ⟨0⟩
  localState := ⟨0⟩
  outstanding := 0
  lifecycle := .died .providerLost

/-- The sent world, with the receiver present and dead. -/
noncomputable def sentWithDeadReceiver : ServerWorld :=
  { sent with
      instances := fun kind current =>
        match kind, current with
        | .listener, _ => none
        | .connection, n => if n = 7 then some deadConnection else none }

theorem sentWithDeadReceiver_slot :
    sentWithDeadReceiver.instances .connection wire.receiver.instanceId
      = some deadConnection := rfl

theorem sentWithDeadReceiver_wire :
    sentWithDeadReceiver.inFlight () wire = pendingLedger := sent_wire

open Classical in
/-- The ledger with the occurrence resolved by its receiver's death. -/
noncomputable def receiverDiedLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun occurrence =>
    if occurrence = escrowed then some (.receiverDied .providerLost) else none
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
theorem receiverDiedLedger_resolution :
    receiverDiedLedger.resolution escrowed = some (.receiverDied .providerLost) := by
  show (if escrowed = escrowed then some (ChannelResolution.receiverDied .providerLost)
    else none) = some (ChannelResolution.receiverDied .providerLost)
  rw [if_pos rfl]

open Classical in
theorem receiverDiedLedger_resolves_nothing_else :
    ResolvesNothingElse pendingLedger receiverDiedLedger escrowed := by
  intro occurrence notIt
  show (if occurrence = escrowed then some (ChannelResolution.receiverDied .providerLost)
    else none) = none
  rw [if_neg notIt]

open Classical in
/-- The world after the receiver's death. -/
noncomputable def afterReceiverDeath : ServerWorld :=
  { sentWithDeadReceiver with
      inFlight := fun _ session =>
        if session = wire then receiverDiedLedger else EscrowLedger.empty }

open Classical in
theorem afterReceiverDeath_wire :
    afterReceiverDeath.inFlight () wire = receiverDiedLedger := by
  show (if wire = wire then receiverDiedLedger else EscrowLedger.empty) = receiverDiedLedger
  rw [if_pos rfl]

open Classical in
theorem afterReceiverDeath_off {session : serverTopology.ChannelId ()}
    (notWire : session ≠ wire) :
    afterReceiverDeath.inFlight () session = EscrowLedger.empty := by
  show (if session = wire then receiverDiedLedger else EscrowLedger.empty) = EscrowLedger.empty
  rw [if_neg notWire]

/--
**A receiver's death.**

The corpus's first, and the half of `endpointDeathIsEarned` that was discharged
`cases isDeath` — vacuously — everywhere. A reviewer pointed out that §10.110's
rule had been half-run: the sender conjunct had a witness and the receiver
conjunct had none. §10.117.
-/
theorem the_receiver_death :
    serverPlan.ResolvesEscrow sentWithDeadReceiver afterReceiverDeath () wire escrowed
      (.receiverDied .providerLost) where
  onItsSession := rfl
  wasOutstanding := by
    rw [sentWithDeadReceiver_wire]
    exact ⟨List.mem_cons_self, rfl⟩
  nowResolved := by rw [afterReceiverDeath_wire]; exact receiverDiedLedger_resolution
  resolvesNothingElse := by
    rw [sentWithDeadReceiver_wire, afterReceiverDeath_wire]
    exact receiverDiedLedger_resolves_nothing_else
  requestsNothing := by
    show RequestsNothing (sentWithDeadReceiver.inFlight () wire)
      (afterReceiverDeath.inFlight () wire)
    rw [sentWithDeadReceiver_wire, afterReceiverDeath_wire]
    exact fun _ => rfl
  ledgerExtends := by
    rw [sentWithDeadReceiver_wire, afterReceiverDeath_wire]
    exact pending_extends_to receiverDiedLedger rfl (by simp [pendingLedger])
  createsOnlyTheCarrier := by
    intro other held fresh
    refine absurd ?_ fresh
    show other ∈ (sentWithDeadReceiver.inFlight () wire).created
    rw [sentWithDeadReceiver_wire]
    have inList : other ∈ (afterReceiverDeath.inFlight () wire).created := held
    rw [afterReceiverDeath_wire] at inList
    exact inList
  carrierOnItsSession := by intro carrier isCoalesce; cases isCoalesce
  carrierIsOutstanding := by intro carrier isCoalesce; cases isCoalesce
  carrierCarriesTheMessage := by intro carrier isCoalesce; cases isCoalesce
  endpointDeathIsEarned := by
    constructor
    · intro reason isDeath
      cases isDeath
    · intro reason isDeath
      cases isDeath
      exact ⟨deadConnection, sentWithDeadReceiver_slot, rfl, rfl⟩
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := fun isWire => outside (by rw [isWire])
      show ledgerAt false session = afterReceiverDeath.inFlight () session
      rw [ledgerAt_off_wire_empty notWire, afterReceiverDeath_off notWire]
    | _ => rfl

/--
**And a process that finished is not a process that died.**

`ProcessLifecycle.Live` is `running` and nothing else, so an earlier version of
`endpointDeathIsEarned` — which asked only `¬ Live` — accepted a `.terminated`
incarnation, one that had *completed its protocol*. `ProcessDeathReason` is
documented as why a process stopped "without finishing".
`Grass/Process/Network/Death.lean` says the same. §10.117.
-/
theorem a_terminated_sender_did_not_die
    {before after : ServerWorld} {reason : ProcessDeathReason}
    {incarnation : ProcessInstance serverTopology}
    (present : before.instances .listener wire.sender.instanceId = some incarnation)
    (finished : ∃ result, incarnation.lifecycle = .terminated result)
    (died : serverPlan.ResolvesEscrow before after () wire escrowed (.senderDied reason)) :
    False := by
  obtain ⟨found, sameSlot, _, itDied⟩ := died.endpointDeathIsEarned.1 reason rfl
  have same : found = incarnation := Option.some.inj (sameSlot.symm.trans present)
  subst same
  obtain ⟨result, terminated⟩ := finished
  rw [terminated] at itDied
  exact absurd itDied (by intro equal; cases equal)

/--
**And a death recorded against a stale reference is refused.**

The other half a reviewer found: the first version read the *slot* and never
compared generations, so a restarted incarnation satisfied a death recorded
against its predecessor. `ProcessRef` splits `instanceId` from `generation`
precisely so a stale reference fails. §10.117.
-/
theorem a_stale_reference_cannot_die
    {before after : ServerWorld} {reason : ProcessDeathReason}
    {incarnation : ProcessInstance serverTopology}
    (present : before.instances .listener wire.sender.instanceId = some incarnation)
    (restarted : incarnation.ref.generation ≠ wire.sender.generation)
    (died : serverPlan.ResolvesEscrow before after () wire escrowed (.senderDied reason)) :
    False := by
  obtain ⟨found, sameSlot, sameGeneration, _⟩ := died.endpointDeathIsEarned.1 reason rfl
  have same : found = incarnation := Option.some.inj (sameSlot.symm.trans present)
  subst same
  exact restarted sameGeneration

/-- **A cancellation request**, which records and does not resolve. -/
theorem the_request : serverPlan.RequestsCancel sent afterRequesting () wire escrowed where
  onItsSession := rfl
  wasOutstanding := by rw [sent_wire]; exact ⟨List.mem_cons_self, rfl⟩
  wasNotRequested := by rw [sent_wire]; simp [pendingLedger]
  nowRequested := by rw [afterRequesting_wire]; exact requestedLedger_requested
  resolvesNothing := by
    rw [sent_wire, afterRequesting_wire]
    exact requestedLedger_resolves_nothing
  createsNothing := by
    show CreatesNothing (sent.inFlight () wire) (afterRequesting.inFlight () wire)
    rw [sent_wire, afterRequesting_wire]
    rfl
  requestsNothingElse := by
    show RequestsNothingElse (sent.inFlight () wire) (afterRequesting.inFlight () wire) escrowed
    rw [sent_wire, afterRequesting_wire]
    exact requestedLedger_requests_nothing_else
  ledgerExtends := by
    rw [sent_wire, afterRequesting_wire]
    exact pending_extends_to requestedLedger rfl (by simp [pendingLedger])
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := fun isWire => outside (by rw [isWire])
      exact off_wire_ledgers notWire afterRequesting (afterRequesting_off notWire)
    | _ => rfl

/-- **And a drop**, which is the plain `ResolvesEscrow` the other five share. -/
theorem the_drop : serverPlan.ResolvesEscrow sent afterDropping () wire escrowed .dropped where
  onItsSession := rfl
  wasOutstanding := by rw [sent_wire]; exact ⟨List.mem_cons_self, rfl⟩
  nowResolved := by rw [afterDropping_wire]; exact droppedLedger_resolution
  resolvesNothingElse := by
    rw [sent_wire, afterDropping_wire]
    exact droppedLedger_resolves_nothing_else
  requestsNothing := by
    show RequestsNothing (sent.inFlight () wire) (afterDropping.inFlight () wire)
    rw [sent_wire, afterDropping_wire]
    exact fun _ => rfl
  carrierOnItsSession := by intro carrier isCoalesce; cases isCoalesce
  carrierIsOutstanding := by intro carrier isCoalesce; cases isCoalesce
  carrierCarriesTheMessage := by intro carrier isCoalesce; cases isCoalesce
  endpointDeathIsEarned := by
    constructor
    · intro reason isDeath
      cases isDeath
    · intro reason isDeath
      cases isDeath
  createsOnlyTheCarrier := by
    intro other held fresh
    exact absurd (by rw [sent_wire]; rw [afterDropping_wire] at held; exact held) fresh
  ledgerExtends := by
    rw [sent_wire, afterDropping_wire]
    exact pending_extends_to droppedLedger rfl (by simp [pendingLedger])
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : ¬ (session = wire) := fun isWire => outside (by rw [isWire])
      exact off_wire_ledgers notWire afterDropping (afterDropping_off notWire)
    | _ => rfl

/-! ## And the refusal the new field supplies -/

/--
**A close may not be recorded against a session the message was never on.**

`onItsSession`. `escrowed`'s own `ChannelId` is `wire`, so a `ClosesSession`
claiming to be about any other session is refused — which is what stops one
occurrence being resolved once on each of two sessions while
`EscrowLedger.atMostOneRecordedEnding` holds of both ledgers.
-/
theorem a_close_on_the_wrong_session_is_refused
    (elsewhere : serverTopology.ChannelId ()) (notWire : elsewhere ≠ wire)
    (before after : ServerWorld) :
    ¬ serverPlan.ClosesSession before after () elsewhere escrowed :=
  fun closes => notWire closes.onItsSession.symm


end Grass.Process.Tests.ChannelStep
