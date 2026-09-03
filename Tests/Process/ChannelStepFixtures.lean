import Tests.Process.TransitionFixtures

/-!
# The channel constructors nothing had ever built

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.79: of `NetworkTransition`'s eleven
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
  nowResolved := by rw [afterClosing_wire]; exact closedLedger_resolution
  closesEverything := by
    intro other outstanding
    rw [only_the_one_is_outstanding outstanding, afterClosing_wire]
    exact closedLedger_resolution
  resolvesOnlyAs := by
    rw [sent_wire, afterClosing_wire]
    exact closedLedger_resolves_nothing_else.resolvesOnlyAs closedLedger_resolution
  createsNothing := by
    show CreatesNothing (sent.inFlight () wire) (afterClosing.inFlight () wire)
    rw [sent_wire, afterClosing_wire]
    rfl
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
  nowResolved := by rw [afterDying_wire]; exact diedLedger_resolution
  killsEverything := by
    intro other outstanding
    rw [only_the_one_is_outstanding outstanding, afterDying_wire]
    exact diedLedger_resolution
  resolvesOnlyAs := by
    rw [sent_wire, afterDying_wire]
    exact diedLedger_resolves_nothing_else.resolvesOnlyAs diedLedger_resolution
  createsNothing := by
    show CreatesNothing (sent.inFlight () wire) (afterDying.inFlight () wire)
    rw [sent_wire, afterDying_wire]
    rfl
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

/-- **A cancellation request**, which records and does not resolve. -/
theorem the_request : serverPlan.RequestsCancel sent afterRequesting () wire escrowed where
  onItsSession := rfl
  wasOutstanding := by rw [sent_wire]; exact ⟨List.mem_cons_self, rfl⟩
  wasNotRequested := by rw [sent_wire]; simp [pendingLedger]
  nowRequested := by rw [afterRequesting_wire]; exact requestedLedger_requested
  stillOutstanding := by
    rw [afterRequesting_wire]
    exact ⟨List.mem_cons_self, rfl⟩
  resolvesNothing := by
    rw [sent_wire, afterRequesting_wire]
    exact requestedLedger_resolves_nothing
  createsNothing := by
    show CreatesNothing (sent.inFlight () wire) (afterRequesting.inFlight () wire)
    rw [sent_wire, afterRequesting_wire]
    rfl
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

/-- **And a drop**, which is the plain `ResolvesEscrow` the other six share. -/
theorem the_drop : serverPlan.ResolvesEscrow sent afterDropping () wire escrowed .dropped where
  onItsSession := rfl
  wasOutstanding := by rw [sent_wire]; exact ⟨List.mem_cons_self, rfl⟩
  nowResolved := by rw [afterDropping_wire]; exact droppedLedger_resolution
  resolvesOnlyAs := by
    rw [sent_wire, afterDropping_wire]
    exact droppedLedger_resolves_nothing_else.resolvesOnlyAs droppedLedger_resolution
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
