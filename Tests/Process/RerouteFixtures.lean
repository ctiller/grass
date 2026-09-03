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

## And what building it found

Trying to prove `WellFormed`'s sixth clause preserved led to a `drop` that
discharged every field `ResolvesEscrow` had while appending an unrelated
occurrence and resolving it `.rerouted` to a session it never touched.
`LedgerExtends` forbids erasing and says nothing about adding, so the step was
legal and the clause was false. `ResolvesNothingElse` is the field that closes
it; `the_stranding_drop_is_refused` is the refusal, and
`the_stranding_ledger_extends` and `the_stranding_scope` show the other fields
really were satisfiable there. §10.87.
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
  resolvesNothingElse := by
    show ResolvesNothingElse (sent.inFlight () wire) (reroutedAt wire) escrowed
    rw [sent_wire, reroutedAt_wire]
    exact fun _ notIt => reroutedLedger_resolution_off notIt
  destinationResolvesNothing := by
    show ResolvesNothing (ledgerAt false sidewire) (reroutedAt sidewire)
    rw [ledgerAt_off_wire_empty sidewire_ne_wire, reroutedAt_sidewire]
    exact fun _ => rfl
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

/-! ## And the step that strands one -/

/--
A second occurrence on the wire, which no send ever put there.

`EscrowLedger.noFabrication` says a *resolved* occurrence must be in `created`,
and `LedgerExtends.createdPrefix` lets a step append to `created`. So a step may
introduce this occurrence and resolve it in the same move.
-/
def stranded : EdgeOccurrence serverTopology World.serverMessage () :=
  ⟨payload, ⟨wire, { id := ⟨.messageOccurrence, 2⟩, isMessage := rfl }⟩⟩

/-- And it is not the occurrence the step is about. -/
theorem stranded_ne_escrowed : stranded ≠ escrowed := by
  intro same
  have ids := congrArg (fun occurrence => occurrence.2.2.id.carrier) same
  simp [stranded, escrowed, occurrenceOf] at ids

open Classical in
/--
The wire's ledger after a drop that also invents a reroute.

`escrowed` is dropped, which is what the step declares. `stranded` is appended
and resolved as rerouted to `sidewire`, which the step declares nothing about.
-/
noncomputable def strandingLedger :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed, stranded]
  rank := fun occurrence => occurrence.2.2.id.carrier
  rankOrdersCreated := by decide
  resolution := fun occurrence =>
    if occurrence = escrowed then some .dropped
    else if occurrence = stranded then some (.rerouted sidewire) else none
  noFabrication := by
    intro occurrence resolved
    by_cases isFirst : occurrence = escrowed
    · simp [isFirst]
    · by_cases isSecond : occurrence = stranded
      · simp [isSecond]
      · simp [isFirst, isSecond] at resolved
  coalesceCarrierLater := by
    intro occurrence carrier merged
    by_cases isFirst : occurrence = escrowed
    · simp [isFirst] at merged
    · by_cases isSecond : occurrence = stranded
      · simp [isSecond, stranded_ne_escrowed] at merged
      · simp [isFirst, isSecond] at merged
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by
    intro occurrence reason acknowledged
    by_cases isFirst : occurrence = escrowed
    · simp [isFirst] at acknowledged
    · by_cases isSecond : occurrence = stranded
      · simp [isSecond, stranded_ne_escrowed] at acknowledged
      · simp [isFirst, isSecond] at acknowledged

open Classical in
/-- Every session's escrow after that drop: the wire's moved, nothing else. -/
noncomputable def strandingAt (session : serverTopology.ChannelId ()) :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) :=
  if session = wire then strandingLedger else EscrowLedger.empty

open Classical in
theorem strandingAt_wire : strandingAt wire = strandingLedger := by
  unfold strandingAt
  rw [if_pos rfl]

open Classical in
theorem strandingAt_off {session : serverTopology.ChannelId ()} (notWire : session ≠ wire) :
    strandingAt session = EscrowLedger.empty := by
  unfold strandingAt
  rw [if_neg notWire]

open Classical in
theorem strandingLedger_drops : strandingLedger.resolution escrowed = some .dropped := by
  show (if escrowed = escrowed then some ChannelResolution.dropped
    else if escrowed = stranded then some (ChannelResolution.rerouted sidewire) else none)
      = some ChannelResolution.dropped
  rw [if_pos rfl]

open Classical in
theorem strandingLedger_strands :
    strandingLedger.resolution stranded = some (.rerouted sidewire) := by
  show (if stranded = escrowed then some ChannelResolution.dropped
    else if stranded = stranded then some (ChannelResolution.rerouted sidewire) else none)
      = some (ChannelResolution.rerouted sidewire)
  rw [if_neg stranded_ne_escrowed, if_pos rfl]

/-- The world after it. -/
noncomputable def afterStranding : ServerWorld :=
  { quiet with inFlight := fun _ => strandingAt }

/--
**The step that strands it, refused.**

Every *other* field of `ResolvesEscrow` is discharged at this pair of worlds, and
that is what made the defect real: `onItsSession` and `nowResolved` are about
`escrowed`, `ledgerExtends` forbids rewriting a resolution and permits appending
to `created`, and `scope` is one session's escrow. Nothing said which *other*
occurrences a step may resolve, so this drop was a legal step of the family and
it takes a network where every reroute lands to one where a payload is rerouted
to a session that never receives it.

`ResolvesNothingElse` is the field that closes it, and this is the refusal.
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.87.
-/
theorem the_stranding_drop_is_refused :
    ¬ serverPlan.ResolvesEscrow sent afterStranding () wire escrowed .dropped := by
  intro drops
  have silent := drops.resolvesNothingElse stranded stranded_ne_escrowed
  rw [show afterStranding.inFlight () wire = strandingLedger from strandingAt_wire,
    show sent.inFlight () wire = pendingLedger from sent_wire,
    strandingLedger_strands] at silent
  exact absurd silent (by intro equal; cases equal)

/--
And the other fields really are all satisfiable there, so the refusal is the
new field's doing and not an accident of the world.
-/
theorem the_stranding_ledger_extends :
    LedgerExtends (sent.inFlight () wire) (afterStranding.inFlight () wire) := by
  show LedgerExtends (sent.inFlight () wire) (strandingAt wire)
  rw [sent_wire, strandingAt_wire]
  exact
    { createdPrefix := ⟨[stranded], rfl⟩
      resolutionPermanent := by
        intro occurrence resolution ended
        exact absurd ended (by simp [pendingLedger])
      cancelRequestMonotone := by
        intro occurrence requested
        exact absurd requested (by simp [pendingLedger]) }

/-- And it is one session's escrow and nothing else. -/
theorem the_stranding_scope :
    serverPlan.TouchesOnly sent afterStranding (fun fragment => fragment = .escrow () wire) := by
  intro fragment outside
  cases fragment with
  | escrow edge session =>
    have sameEdge : edge = () := rfl
    subst sameEdge
    have notWire : session ≠ wire := fun isWire => outside (by rw [isWire])
    show ledgerAt false session = strandingAt session
    rw [ledgerAt_off_wire_empty notWire, strandingAt_off notWire]
  | _ => rfl

/-- Before the step, every reroute lands, because nothing is resolved at all. -/
theorem sent_reroutes_land : sent.ReroutesLand := by
  intro edge session occurrence destination rerouted
  have sameEdge : edge = () := rfl
  subst sameEdge
  by_cases isWire : session = wire
  · subst isWire
    rw [sent_wire] at rerouted
    exact absurd rerouted (by simp [pendingLedger])
  · rw [show sent.inFlight () session = ledgerAt false session from rfl,
      ledgerAt_off_wire_empty isWire] at rerouted
    exact absurd rerouted (by simp [EscrowLedger.empty])

/--
**And at `afterStranding`, one does not.**

The world the refused step would have reached, shown to be genuinely bad rather
than merely unreachable. `LogicalProcessNetworkCore.WellFormed`'s sixth clause
fails here: a payload is rerouted to a session whose ledger holds nothing.

The missing constraint was never `LedgerExtends`, which does its job — nothing is
erased or reordered here, and `the_stranding_ledger_extends` proves it. It was
that no constructor bounded which occurrences *other* than its own it may
resolve. `ResolvesNothingElse` is that bound, and
`the_stranding_drop_is_refused` is it working.
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.87.
-/
theorem the_stranding_drop_breaks_reroutesLand : ¬ afterStranding.ReroutesLand := by
  intro lands
  obtain ⟨arrival, arrived⟩ := lands () wire stranded sidewire (by
    show (strandingAt wire).resolution stranded = some (.rerouted sidewire)
    rw [strandingAt_wire]
    exact strandingLedger_strands)
  have empty : afterStranding.inFlight () sidewire = EscrowLedger.empty := by
    show strandingAt sidewire = EscrowLedger.empty
    exact strandingAt_off sidewire_ne_wire
  rw [empty] at arrived
  exact absurd arrived (by simp [EscrowLedger.empty])

end Grass.Process.Tests.Reroute
