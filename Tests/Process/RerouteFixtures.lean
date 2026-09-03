import Tests.Process.ChannelStepFixtures

/-!
# The reroute: the last of the eleven channel constructors

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.79 held `Reroutes` back on the grounds
that it "needs two sessions on one edge and this topology names one", so building
it would be a change to the fixture *world* rather than an addition beside it.

**That was wrong, and wrong in the direction the ledger keeps being wrong in:
it was an argument, not a construction.** A `ChannelId` is two endpoints *and an
epoch*, and §3 put the epoch there precisely so that one edge between one pair of
incarnations can carry more than one session — "dropping the epoch and
identifying a session by its endpoints would let a closed-and-reopened channel
inherit the old session's in-flight messages". So a second session on this edge
is `wire` with a later epoch, and this file is an addition beside the fixture
after all.

What the witness is worth beyond the count. `Reroutes.arrives` was strengthened
after local adversarial review built a reroute that delivered nothing and showed
the after-world still satisfied `LogicalProcessNetworkCore.ReroutesLand`; the
field now says the destination *gained* an occurrence carrying this message.
`the_reroute` is the first step that has ever had to supply it, and
`the_reroute_lands` is the cross-ledger obligation
`Grass/Process/Network/Escrow.lean` records and cannot discharge, discharged.

`a_reroute_to_the_same_session_is_refused` is the other half: `elsewhere` is what
stops a "reroute" that names its own session and therefore moves nothing.
-/

namespace Grass.Process.Tests.Reroute

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld quiet)
open Grass.Process.Tests.Channel (wire)
open Grass.Process.Tests.Transition
  (serverPlan payload occurrenceOf escrowed pendingLedger sent sent_wire
   ledgerAt ledgerAt_off_wire_empty)

/-! ## A second session on the same edge -/

/--
The same two incarnations, a later epoch.

This is the whole of what §10.79 thought needed a new world: `ChannelId.epoch`
already distinguishes two sessions of one channel between one pair of endpoints.
-/
def sidewire : serverTopology.ChannelId () where
  sender := Instances.listenerZero
  receiver := connectionSeven 0
  epoch := ⟨.channelEpoch, 1⟩
  isEpoch := rfl

/-- And it is a different session, which is what `Reroutes.elsewhere` wants. -/
theorem sidewire_ne_wire : sidewire ≠ wire := by
  intro same
  have epochs := congrArg (fun session => session.epoch.carrier) same
  simp [sidewire, wire] at epochs

/-- The occurrence that arrives on it: this message, that session, its own id. -/
def arrival : EdgeOccurrence serverTopology World.serverMessage () :=
  ⟨payload, ⟨sidewire, { id := ⟨.messageOccurrence, 1⟩, isMessage := rfl }⟩⟩

/-- It carries the message the rerouted occurrence carried, which is
`Reroutes.arrives`'s third conjunct. -/
theorem arrival_carries_the_message : arrival.1 = escrowed.1 := rfl

/-! ## The two ledgers the step moves -/

open Classical in
/-- The wire's ledger with its one occurrence resolved as rerouted to
`sidewire`. -/
noncomputable def reroutedLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun occurrence =>
    if occurrence = escrowed then some (.rerouted sidewire) else none
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

/-- And the destination's, which gains the arrival and holds it in flight. -/
noncomputable def arrivedLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [arrival]
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun _ => none
  noFabrication := by simp
  coalesceCarrierLater := by simp
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by simp

open Classical in
/-- The escrow of every session after the reroute: two of them moved. -/
noncomputable def reroutedAt (session : serverTopology.ChannelId ()) :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) :=
  if session = wire then reroutedLedger
  else if session = sidewire then arrivedLedger
  else EscrowLedger.empty

open Classical in
theorem reroutedAt_wire : reroutedAt wire = reroutedLedger := by
  unfold reroutedAt
  rw [if_pos rfl]

open Classical in
theorem reroutedAt_sidewire : reroutedAt sidewire = arrivedLedger := by
  unfold reroutedAt
  rw [if_neg sidewire_ne_wire, if_pos rfl]

open Classical in
theorem reroutedAt_elsewhere {session : serverTopology.ChannelId ()}
    (notWire : session ≠ wire) (notSide : session ≠ sidewire) :
    reroutedAt session = EscrowLedger.empty := by
  unfold reroutedAt
  rw [if_neg notWire, if_neg notSide]

open Classical in
theorem reroutedLedger_resolution :
    reroutedLedger.resolution escrowed = some (.rerouted sidewire) := by
  show (if escrowed = escrowed then some (ChannelResolution.rerouted sidewire) else none)
    = some (ChannelResolution.rerouted sidewire)
  rw [if_pos rfl]

open Classical in
/-- And nothing else on the wire is resolved at all, which is what an
`Outstanding` claim off `escrowed` would need. -/
theorem reroutedLedger_resolution_off {occurrence : EdgeOccurrence serverTopology
    World.serverMessage ()} (notIt : occurrence ≠ escrowed) :
    reroutedLedger.resolution occurrence = none := by
  show (if occurrence = escrowed then some (ChannelResolution.rerouted sidewire) else none)
    = none
  rw [if_neg notIt]

/-- The world after the reroute. -/
noncomputable def afterReroute : ServerWorld :=
  { quiet with inFlight := fun _ => reroutedAt }

/-! ## The step -/

/--
**A reroute: the last channel constructor the corpus had never built.**

Every field is discharged at a world a send actually reached, and `arrives` is
discharged by an occurrence the destination did not hold before it.
-/
theorem the_reroute : serverPlan.Reroutes sent afterReroute () wire escrowed sidewire where
  onItsSession := rfl
  wasOutstanding := by
    show (sent.inFlight () wire).Outstanding escrowed
    rw [sent_wire]
    exact ⟨List.mem_cons_self, rfl⟩
  nowResolved := by
    show (reroutedAt wire).resolution escrowed = some (.rerouted sidewire)
    rw [reroutedAt_wire]
    exact reroutedLedger_resolution
  ledgerExtends := by
    show LedgerExtends (sent.inFlight () wire) (reroutedAt wire)
    rw [sent_wire, reroutedAt_wire]
    exact
      { createdPrefix := List.prefix_rfl
        resolutionPermanent := by
          intro occurrence resolution ended
          exact absurd ended (by simp [pendingLedger])
        cancelRequestMonotone := by
          intro occurrence requested
          exact absurd requested (by simp [pendingLedger]) }
  elsewhere := sidewire_ne_wire
  arrives := by
    refine ⟨arrival, ?_, ?_, arrival_carries_the_message⟩
    · show arrival ∉ (ledgerAt false sidewire).created
      rw [ledgerAt_off_wire_empty sidewire_ne_wire]
      exact List.not_mem_nil
    · show arrival ∈ (reroutedAt sidewire).created
      rw [reroutedAt_sidewire]
      exact List.mem_cons_self
  destinationExtends := by
    show LedgerExtends (ledgerAt false sidewire) (reroutedAt sidewire)
    rw [ledgerAt_off_wire_empty sidewire_ne_wire, reroutedAt_sidewire]
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
      have notWire : session ≠ wire := fun isWire => outside (Or.inl (by rw [isWire]))
      have notSide : session ≠ sidewire := fun isSide => outside (Or.inr (by rw [isSide]))
      show ledgerAt false session = reroutedAt session
      rw [ledgerAt_off_wire_empty notWire, reroutedAt_elsewhere notWire notSide]
    | _ => rfl

/-! ## What it buys -/

/--
**The cross-ledger obligation, discharged.**

`Grass/Process/Network/Escrow.lean` records `ReroutedElsewhere` as an obligation
one ledger cannot check, and `Grass/Process/Network/World.lean` makes it
`ReroutesLand` over every session at once. This is the after-world satisfying it
at the session the reroute resolved.
-/
theorem the_reroute_lands :
    (afterReroute.inFlight () wire).ReroutedElsewhere
      (fun destination arrived => arrived ∈ (afterReroute.inFlight () destination).created) := by
  intro occurrence destination rerouted
  refine ⟨arrival, ?_⟩
  have sameDestination : destination = sidewire := by
    have resolved : (reroutedAt wire).resolution occurrence = some (.rerouted destination) :=
      rerouted
    rw [reroutedAt_wire] at resolved
    by_cases isIt : occurrence = escrowed
    · subst isIt
      rw [reroutedLedger_resolution] at resolved
      cases resolved
      rfl
    · rw [reroutedLedger_resolution_off isIt] at resolved
      exact absurd resolved (by intro equal; cases equal)
  subst sameDestination
  show arrival ∈ (reroutedAt sidewire).created
  rw [reroutedAt_sidewire]
  exact List.mem_cons_self

/--
**And a reroute that names its own session is refused.**

`elsewhere` is the field that makes a reroute a movement. Without it, resolving
an occurrence as `.rerouted` to the session it is already on would satisfy
`arrives` from the ledger it is leaving, and `ReroutesLand` would hold with
nothing having moved anywhere.
-/
theorem a_reroute_to_the_same_session_is_refused
    (rerouted : serverPlan.Reroutes sent afterReroute () wire escrowed wire) : False :=
  rerouted.elsewhere rfl

end Grass.Process.Tests.Reroute
