import Tests.Process.RerouteFixtures

/-!
# Closing a session with two messages in flight

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.90. `ChannelResolution.channelClosed`
exists because "an occurrence in flight at an ordinary close has no ending, and
would either strand live forever or have to be misrecorded as a death". An
earlier version of `ClosesSession` did not deliver the close that rationale
describes: it named *one* occurrence, said nothing about the rest, and — under
the first version of §10.87's repair — positively forbade ending them.

Local adversarial review built the world that shows it: two ordinary sends on one
session, then a close. The second message is left `Outstanding` on a `.closed`
session, and `ClosesSession.wasOpen` and `KillsSession.wasOpen` refuse every later
close or death, so it strands or a `drop` misrecords it.

`closesEverything` is the field, `ResolvesOnlyAs` replaced `ResolvesNothingElse`
so that the field is satisfiable, and this file is both halves: `the_full_close`
is a close that ends both, and `a_close_that_leaves_one_behind_is_refused` is the
one that does not.

The world is reachable rather than manufactured: `the_second_send` is an ordinary
`SendsEscrow` from `sent`, so `sent2` is two sends into a run of this plan.
-/

namespace Grass.Process.Tests.Close

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld quiet)
open Grass.Process.Tests.Channel (wire)
open Grass.Process.Tests.Transition
  (serverPlan payload escrowed pendingLedger sent sent_wire ledgerAt
   ledgerAt_off_wire_empty cursorAt cursorAt_off_wire)
open Grass.Process.Tests.Reroute (stranded stranded_ne_escrowed)

/-! ## A second message on the same wire -/

/-- Its occurrence, which is `stranded`'s. -/
def strandedOccurrence : serverTopology.ChannelOccurrence () payload := stranded.2

/-- The wire's ledger with both messages in flight. -/
noncomputable def twoPending :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed, stranded]
  rank := fun occurrence => occurrence.2.2.id.carrier
  rankOrdersCreated := by decide
  resolution := fun _ => none
  noFabrication := by simp
  coalesceCarrierLater := by simp
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by simp

open Classical in
/-- Every session's escrow after the second send. -/
noncomputable def twoPendingAt (session : serverTopology.ChannelId ()) :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) :=
  if session = wire then twoPending else EscrowLedger.empty

open Classical in
theorem twoPendingAt_wire : twoPendingAt wire = twoPending := by
  unfold twoPendingAt
  rw [if_pos rfl]

open Classical in
theorem twoPendingAt_off {session : serverTopology.ChannelId ()} (notWire : session ≠ wire) :
    twoPendingAt session = EscrowLedger.empty := by
  unfold twoPendingAt
  rw [if_neg notWire]

/-- The world after both sends. -/
noncomputable def sent2 : ServerWorld :=
  { quiet with inFlight := fun _ => twoPendingAt }

theorem sent2_wire : sent2.inFlight () wire = twoPending := twoPendingAt_wire

/--
**And it is reachable: an ordinary second send gets there.**

Without this the two-message world would be manufactured, and a fixture that
manufactures the world its own complaint needs is not evidence of anything. This
is `liveSteps.Send` again, at the same plan, one step further on.
-/
theorem the_second_send : serverPlan.SendsEscrow sent sent2 () payload strandedOccurrence where
  contractual :=
    ⟨rfl, rfl,
      by rw [sent_wire]
         intro held
         have inList : stranded ∈ [escrowed] := held
         exact stranded_ne_escrowed (by simpa using inList),
      by rw [sent2_wire]; exact ⟨List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩⟩
  wasFresh := by
    show stranded ∉ (sent.inFlight () wire).created
    rw [sent_wire]
    intro held
    have inList : stranded ∈ [escrowed] := held
    exact stranded_ne_escrowed (by simpa using inList)
  nowEscrowed := by
    show (sent2.inFlight () wire).Outstanding stranded
    rw [sent2_wire]
    exact ⟨List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  resolvesNothing := by
    show ResolvesNothing (sent.inFlight () wire) (sent2.inFlight () wire)
    rw [sent_wire, sent2_wire]
    exact fun _ => rfl
  requestsNothing := by
    show RequestsNothing (sent.inFlight () wire) (sent2.inFlight () wire)
    rw [sent_wire, sent2_wire]
    exact fun _ => rfl
  createsOnlyTheMessage := by
    intro other held fresh
    show other = stranded
    have onWire : other ∈ (sent2.inFlight () wire).created := held
    rw [sent2_wire] at onWire
    have inList : other ∈ [escrowed, stranded] := onWire
    rcases List.mem_cons.mp inList with isFirst | rest
    · subst isFirst
      refine absurd ?_ fresh
      show escrowed ∈ (sent.inFlight () wire).created
      rw [sent_wire]
      exact List.mem_cons_self
    · exact List.mem_singleton.mp rest
  ledgerExtends := by
    show LedgerExtends (sent.inFlight () wire) (sent2.inFlight () wire)
    rw [sent_wire, sent2_wire]
    exact
      { createdPrefix := ⟨[stranded], rfl⟩
        resolutionPermanent := by
          intro occurrence resolution ended
          exact absurd ended (by simp [pendingLedger])
        cancelRequestMonotone := by
          intro occurrence requested
          exact absurd requested (by simp [pendingLedger]) }
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : session ≠ wire := by
        intro isWire
        subst isWire
        exact outside rfl
      show ledgerAt false session = twoPendingAt session
      rw [ledgerAt_off_wire_empty notWire, twoPendingAt_off notWire]
    | _ => rfl

/-- Both are in flight there. -/
theorem both_are_outstanding :
    (sent2.inFlight () wire).Outstanding escrowed ∧
      (sent2.inFlight () wire).Outstanding stranded := by
  rw [sent2_wire]
  exact ⟨⟨List.mem_cons_self, rfl⟩, ⟨List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩⟩

/-! ## The close that ends both, and the one that does not -/

open Classical in
/-- The wire's ledger with both messages closed. -/
noncomputable def bothClosed :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed, stranded]
  rank := fun occurrence => occurrence.2.2.id.carrier
  rankOrdersCreated := by decide
  resolution := fun occurrence =>
    if occurrence = escrowed then some .channelClosed
    else if occurrence = stranded then some .channelClosed else none
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
theorem bothClosed_first : bothClosed.resolution escrowed = some .channelClosed := by
  show (if escrowed = escrowed then some ChannelResolution.channelClosed
    else if escrowed = stranded then some ChannelResolution.channelClosed else none)
      = some ChannelResolution.channelClosed
  rw [if_pos rfl]

open Classical in
theorem bothClosed_second : bothClosed.resolution stranded = some .channelClosed := by
  show (if stranded = escrowed then some ChannelResolution.channelClosed
    else if stranded = stranded then some ChannelResolution.channelClosed else none)
      = some ChannelResolution.channelClosed
  rw [if_neg stranded_ne_escrowed, if_pos rfl]

open Classical in
theorem bothClosed_other {occurrence : EdgeOccurrence serverTopology World.serverMessage ()}
    (notFirst : occurrence ≠ escrowed) (notSecond : occurrence ≠ stranded) :
    bothClosed.resolution occurrence = none := by
  show (if occurrence = escrowed then some ChannelResolution.channelClosed
    else if occurrence = stranded then some ChannelResolution.channelClosed else none) = none
  rw [if_neg notFirst, if_neg notSecond]

open Classical in
/-- The world after a close that ends both. -/
noncomputable def afterFullClose : ServerWorld :=
  { sent2 with
      inFlight := fun _ session => if session = wire then bothClosed else EscrowLedger.empty
      sessions := fun _ session =>
        if session = wire then { cursorAt false wire with status := .closed }
        else cursorAt false session }

open Classical in
theorem afterFullClose_wire : afterFullClose.inFlight () wire = bothClosed := by
  show (if wire = wire then bothClosed else EscrowLedger.empty) = bothClosed
  rw [if_pos rfl]

open Classical in
theorem afterFullClose_off {session : serverTopology.ChannelId ()} (notWire : session ≠ wire) :
    afterFullClose.inFlight () session = EscrowLedger.empty := by
  show (if session = wire then bothClosed else EscrowLedger.empty) = EscrowLedger.empty
  rw [if_neg notWire]

open Classical in
theorem afterFullClose_sessions_off {session : serverTopology.ChannelId ()}
    (notWire : session ≠ wire) :
    afterFullClose.sessions () session = cursorAt false session := by
  show (if session = wire then { cursorAt false wire with status := .closed }
    else cursorAt false session) = cursorAt false session
  rw [if_neg notWire]

/--
**A close that ends both messages.**

The close `ChannelResolution.channelClosed`'s docstring describes, and the first
one this corpus can express: `closesEverything` is discharged at a session with
two occurrences in flight, so it is not the vacuous "all one of them" the
one-message fixture gives.
-/
theorem the_full_close : serverPlan.ClosesSession sent2 afterFullClose () wire escrowed where
  onItsSession := rfl
  wasOutstanding := both_are_outstanding.1
  closesEverything := by
    intro other _ outstanding
    rw [sent2_wire] at outstanding
    have held : other ∈ [escrowed, stranded] := outstanding.1
    rw [afterFullClose_wire]
    rcases List.mem_cons.mp held with isFirst | rest
    · rw [isFirst]; exact bothClosed_first
    · rw [List.mem_singleton.mp rest]; exact bothClosed_second
  ledgerExtends := by
    rw [sent2_wire, afterFullClose_wire]
    exact
      { createdPrefix := List.prefix_rfl
        resolutionPermanent := by
          intro occurrence resolution ended
          exact absurd ended (by intro equal; cases equal)
        cancelRequestMonotone := by
          intro occurrence requested
          exact absurd requested (by intro equal; cases equal) }
  createsNothing := by
    show CreatesNothing (sent2.inFlight () wire) (afterFullClose.inFlight () wire)
    rw [sent2_wire, afterFullClose_wire]
    rfl
  requestsNothing := by
    show RequestsNothing (sent2.inFlight () wire) (afterFullClose.inFlight () wire)
    rw [sent2_wire, afterFullClose_wire]
    exact fun _ => rfl
  resolvesOnlyAs := by
    rw [sent2_wire, afterFullClose_wire]
    intro occurrence moved
    by_cases isFirst : occurrence = escrowed
    · rw [isFirst]; exact bothClosed_first
    · by_cases isSecond : occurrence = stranded
      · rw [isSecond]; exact bothClosed_second
      · exact absurd (bothClosed_other isFirst isSecond) moved
  wasOpen := rfl
  nowClosed := by simp [afterFullClose]
  cursorUnchanged := by simp [afterFullClose, sent2, cursorAt, Grass.Process.Tests.World.quiet]
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : session ≠ wire := fun isWire => outside (Or.inl (by rw [isWire]))
      show twoPendingAt session = afterFullClose.inFlight () session
      rw [twoPendingAt_off notWire, afterFullClose_off notWire]
    | session edge current =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : current ≠ wire := fun isWire => outside (Or.inr (by rw [isWire]))
      show sent2.sessions () current = afterFullClose.sessions () current
      rw [afterFullClose_sessions_off notWire, cursorAt_off_wire notWire]
      rfl
    | _ => rfl

open Classical in
/-- The wire's ledger with only the first message closed. -/
noncomputable def onlyOneClosed :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed, stranded]
  rank := fun occurrence => occurrence.2.2.id.carrier
  rankOrdersCreated := by decide
  resolution := fun occurrence =>
    if occurrence = escrowed then some .channelClosed else none
  noFabrication := by
    intro occurrence resolved
    by_cases isFirst : occurrence = escrowed
    · simp [isFirst]
    · simp [isFirst] at resolved
  coalesceCarrierLater := by
    intro occurrence carrier merged
    by_cases isFirst : occurrence = escrowed
    · simp [isFirst] at merged
    · simp [isFirst] at merged
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by
    intro occurrence reason acknowledged
    by_cases isFirst : occurrence = escrowed
    · simp [isFirst] at acknowledged
    · simp [isFirst] at acknowledged

open Classical in
theorem onlyOneClosed_second : onlyOneClosed.resolution stranded = none := by
  show (if stranded = escrowed then some ChannelResolution.channelClosed else none) = none
  rw [if_neg stranded_ne_escrowed]

open Classical in
/-- The world after a close that leaves the second message in flight. -/
noncomputable def afterPartialClose : ServerWorld :=
  { sent2 with
      inFlight := fun _ session => if session = wire then onlyOneClosed else EscrowLedger.empty
      sessions := fun _ session =>
        if session = wire then { cursorAt false wire with status := .closed }
        else cursorAt false session }

open Classical in
theorem afterPartialClose_wire : afterPartialClose.inFlight () wire = onlyOneClosed := by
  show (if wire = wire then onlyOneClosed else EscrowLedger.empty) = onlyOneClosed
  rw [if_pos rfl]

/--
**And a close that leaves one behind is refused.**

`closesEverything`, biting. Before it, this step was legal and its after-world
held a message `Outstanding` on a `.closed` session, which no later close or
death can reach — `wasOpen` refuses both — so the only remaining ending was a
`drop` recording something that did not happen.
-/
theorem a_close_that_leaves_one_behind_is_refused :
    ¬ serverPlan.ClosesSession sent2 afterPartialClose () wire escrowed := by
  intro closes
  have ended := closes.closesEverything stranded rfl both_are_outstanding.2
  rw [afterPartialClose_wire, onlyOneClosed_second] at ended
  exact absurd ended (by intro equal; cases equal)

/--
And the strand it refuses is a real one: at `afterPartialClose` the second
message is still in flight on a session that is closed.
-/
theorem the_strand_is_real :
    (afterPartialClose.inFlight () wire).Outstanding stranded ∧
      (afterPartialClose.sessions () wire).status = .closed := by
  refine ⟨?_, by simp [afterPartialClose]⟩
  rw [afterPartialClose_wire]
  exact ⟨List.mem_cons_of_mem _ List.mem_cons_self, onlyOneClosed_second⟩

/-! ## And the drop that sends -/

open Classical in
/--
The wire's ledger after a drop that also conjures the second message into flight.

`created` gains `stranded`, unresolved. `LedgerExtends.createdPrefix` permits it —
occurrences are only appended — and `ResolvesOnlyAs` says nothing, because
nothing was *resolved* about it.
-/
noncomputable def fabricated :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed, stranded]
  rank := fun occurrence => occurrence.2.2.id.carrier
  rankOrdersCreated := by decide
  resolution := fun occurrence => if occurrence = escrowed then some .dropped else none
  noFabrication := by
    intro occurrence resolved
    by_cases isFirst : occurrence = escrowed
    · simp [isFirst]
    · simp [isFirst] at resolved
  coalesceCarrierLater := by
    intro occurrence carrier merged
    by_cases isFirst : occurrence = escrowed
    · simp [isFirst] at merged
    · simp [isFirst] at merged
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by
    intro occurrence reason acknowledged
    by_cases isFirst : occurrence = escrowed
    · simp [isFirst] at acknowledged
    · simp [isFirst] at acknowledged

open Classical in
theorem fabricated_second : fabricated.resolution stranded = none := by
  show (if stranded = escrowed then some ChannelResolution.dropped else none) = none
  rw [if_neg stranded_ne_escrowed]

open Classical in
/-- The world after it. -/
noncomputable def afterFabricate : ServerWorld :=
  { quiet with
      inFlight := fun _ session => if session = wire then fabricated else EscrowLedger.empty }

open Classical in
theorem afterFabricate_wire : afterFabricate.inFlight () wire = fabricated := by
  show (if wire = wire then fabricated else EscrowLedger.empty) = fabricated
  rw [if_pos rfl]

/--
**A drop that escrows a message nothing sent is refused.**

`createsOnlyTheCarrier`, biting. Before it, `ledgerExtends` permitted the append
and `resolvesOnlyAs` said nothing about an occurrence that gains no resolution —
so a drop could put a message in flight. Local adversarial review built it and
proved what makes it more than untidy: at the after-world the edge contract's
escrow assertion *holds* of that message, and `docs/PROCESS.md` §3 gives only a
send that power. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.91.
-/
theorem a_drop_that_conjures_a_message_is_refused :
    ¬ serverPlan.ResolvesEscrow sent afterFabricate () wire escrowed .dropped := by
  intro drops
  have onlyCarrier := drops.createsOnlyTheCarrier stranded (by
    show stranded ∈ (afterFabricate.inFlight () wire).created
    rw [afterFabricate_wire]
    exact List.mem_cons_of_mem _ List.mem_cons_self) (by
    show stranded ∉ (sent.inFlight () wire).created
    rw [sent_wire]
    intro held
    have inList : stranded ∈ [escrowed] := held
    exact stranded_ne_escrowed (List.mem_singleton.mp inList))
  exact absurd onlyCarrier (by intro equal; cases equal)

/--
And what it would have escrowed is a message that really was not in flight
before the step and really is after it — so the refusal is not about a
distinction without a difference.
-/
theorem the_conjured_message_would_be_in_flight :
    ¬ (sent.inFlight () wire).Outstanding stranded ∧
      (afterFabricate.inFlight () wire).Outstanding stranded := by
  constructor
  · intro outstanding
    rw [sent_wire] at outstanding
    have inList : stranded ∈ [escrowed] := outstanding.1
    exact stranded_ne_escrowed (List.mem_singleton.mp inList)
  · rw [afterFabricate_wire]
    exact ⟨List.mem_cons_of_mem _ List.mem_cons_self, fabricated_second⟩

/--
**And no later close or death can reach it.**

Both demand `wasOpen`, and the session is closed. This is the half the module
docstring asserted and did not compile — a reviewer pointed out that
`the_strand_is_real` proves the status and stops there, leaving the "strands
forever" claim as prose. It is two lines, so there was no reason for it to be.
-/
theorem no_later_close_reaches_the_strand
    {after : ServerWorld} {occurrence : EdgeOccurrence serverTopology World.serverMessage ()} :
    ¬ serverPlan.ClosesSession afterPartialClose after () wire occurrence := by
  intro closes
  have wasOpen := closes.wasOpen
  rw [the_strand_is_real.2] at wasOpen
  cases wasOpen

/-- And neither can a death. -/
theorem no_later_death_reaches_the_strand
    {after : ServerWorld} {occurrence : EdgeOccurrence serverTopology World.serverMessage ()} :
    ¬ serverPlan.KillsSession afterPartialClose after () wire occurrence := by
  intro kills
  have wasOpen := kills.wasOpen
  rw [the_strand_is_real.2] at wasOpen
  cases wasOpen

/-! ## And the cancellation request that was never made -/

/--
**An acknowledgement acknowledges a request that was already made.**

`EscrowLedger.acknowledgedWasRequested` is a law of one ledger: an
acknowledgement in it needs a request in it. It says nothing about *when* the
request arrived, so a reviewer compiled an `acknowledgeCancel` from `sent` —
where `cancelRequested` is `false` for every occurrence — that writes the request
and the acknowledgement in the same move. `ProcessPlan.RequestsCancel`, with all
its guards, was bypassable entirely, and §3's affine cancellation request was
enforced by nothing. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.97.
-/
theorem an_acknowledgement_needs_a_request
    {before after : ServerWorld} {reason : CancelReason}
    (nothingRequested : (before.inFlight () wire).cancelRequested escrowed = false)
    (acknowledged : serverPlan.ResolvesEscrow before after () wire escrowed
      (.cancelAcknowledged reason)) : False := by
  have requested := acknowledged.acknowledgesARequest
  rw [nothingRequested] at requested
  exact absurd requested (by decide)

/-- Nothing is requested at `sent`, so no acknowledgement can start there. -/
theorem nothing_is_requested_yet
    (occurrence : EdgeOccurrence serverTopology World.serverMessage ()) :
    (sent.inFlight () wire).cancelRequested occurrence = false := by
  rw [sent_wire]
  rfl

/-- **And a request primes only the occurrence it names.** -/
theorem a_request_may_not_prime_another
    {before after : ServerWorld} {other : EdgeOccurrence serverTopology World.serverMessage ()}
    (notIt : other ≠ escrowed)
    (wasNot : (before.inFlight () wire).cancelRequested other = false)
    (nowIs : (after.inFlight () wire).cancelRequested other = true)
    (requested : serverPlan.RequestsCancel before after () wire escrowed) : False := by
  have unchanged := requested.requestsNothingElse other notIt
  rw [nowIs, wasNot] at unchanged
  exact absurd unchanged (by decide)

/-! ## And the coalesce nothing had ever built -/

/--
The occurrence two messages merge into: on this session, with a later identity.

`EscrowLedger.coalesceCarrierLater` requires both — in this ledger, and strictly
later in the rank order — and `ResolvesEscrow.carrierOnItsSession` requires the
first. §10.100 added that field and a reviewer then pointed out that no
`coalesce` had ever been constructed anywhere in the corpus, so the field had no
satisfiability half: two refusals and no witness is how a side condition that
forbids everything looks from outside. §10.110.
-/
def carrier : EdgeOccurrence serverTopology World.serverMessage () :=
  ⟨payload, ⟨wire, { id := ⟨.messageOccurrence, 5⟩, isMessage := rfl }⟩⟩

theorem carrier_ne_escrowed : carrier ≠ escrowed := by
  intro same
  have ids := congrArg (fun occurrence => occurrence.2.2.id.carrier) same
  simp [carrier, escrowed, Transition.occurrenceOf] at ids

open Classical in
/-- The wire's ledger after the merge: the carrier escrowed, the first source
resolved into it, the second still in flight. -/
noncomputable def merged :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed, stranded, carrier]
  rank := fun occurrence => occurrence.2.2.id.carrier
  rankOrdersCreated := by decide
  resolution := fun occurrence =>
    if occurrence = escrowed then some (.coalesced carrier) else none
  noFabrication := by
    intro occurrence resolved
    by_cases isFirst : occurrence = escrowed
    · simp [isFirst]
    · simp [isFirst] at resolved
  coalesceCarrierLater := by
    intro occurrence carrier' isMerge
    by_cases isFirst : occurrence = escrowed
    · subst isFirst
      rw [if_pos rfl] at isMerge
      cases isMerge
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by decide⟩
    · rw [if_neg isFirst] at isMerge
      cases isMerge
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by
    intro occurrence reason acknowledged
    by_cases isFirst : occurrence = escrowed
    · simp [isFirst] at acknowledged
    · simp [isFirst] at acknowledged

open Classical in
theorem merged_first : merged.resolution escrowed = some (.coalesced carrier) := by
  show (if escrowed = escrowed then some (ChannelResolution.coalesced carrier) else none)
    = some (.coalesced carrier)
  rw [if_pos rfl]

open Classical in
theorem merged_other {occurrence : EdgeOccurrence serverTopology World.serverMessage ()}
    (notFirst : occurrence ≠ escrowed) : merged.resolution occurrence = none := by
  show (if occurrence = escrowed then some (ChannelResolution.coalesced carrier) else none)
    = none
  rw [if_neg notFirst]

open Classical in
/-- The world after it. -/
noncomputable def afterCoalesce : ServerWorld :=
  { sent2 with
      inFlight := fun _ session => if session = wire then merged else EscrowLedger.empty }

open Classical in
theorem afterCoalesce_wire : afterCoalesce.inFlight () wire = merged := by
  show (if wire = wire then merged else EscrowLedger.empty) = merged
  rw [if_pos rfl]

open Classical in
theorem afterCoalesce_off {session : serverTopology.ChannelId ()} (notWire : session ≠ wire) :
    afterCoalesce.inFlight () session = EscrowLedger.empty := by
  show (if session = wire then merged else EscrowLedger.empty) = EscrowLedger.empty
  rw [if_neg notWire]

/--
**A coalesce: the constructor nothing in this corpus had ever built.**

Every field of `ResolvesEscrow` at `.coalesced`, including §10.100's
`carrierOnItsSession` — which had two refusals and no witness until this.
-/
theorem the_coalesce :
    serverPlan.ResolvesEscrow sent2 afterCoalesce () wire escrowed (.coalesced carrier) where
  onItsSession := rfl
  wasOutstanding := both_are_outstanding.1
  nowResolved := by rw [afterCoalesce_wire]; exact merged_first
  resolvesNothingElse := by
    rw [sent2_wire, afterCoalesce_wire]
    intro other notIt
    rw [merged_other notIt]
    rfl
  requestsNothing := by
    show RequestsNothing (sent2.inFlight () wire) (afterCoalesce.inFlight () wire)
    rw [sent2_wire, afterCoalesce_wire]
    exact fun _ => rfl
  ledgerExtends := by
    rw [sent2_wire, afterCoalesce_wire]
    exact
      { createdPrefix := ⟨[carrier], rfl⟩
        resolutionPermanent := by
          intro occurrence resolution ended
          exact absurd ended (by intro equal; cases equal)
        cancelRequestMonotone := by
          intro occurrence requested
          exact absurd requested (by intro equal; cases equal) }
  createsOnlyTheCarrier := by
    intro other held fresh
    have inList : other ∈ (afterCoalesce.inFlight () wire).created := held
    rw [afterCoalesce_wire] at inList
    have three : other ∈ [escrowed, stranded, carrier] := inList
    rcases List.mem_cons.mp three with isFirst | rest
    · exact absurd (by rw [isFirst, sent2_wire]; exact List.mem_cons_self) fresh
    · rcases List.mem_cons.mp rest with isSecond | last
      · refine absurd ?_ fresh
        rw [isSecond, sent2_wire]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [List.mem_singleton.mp last]
  carrierOnItsSession := by
    intro carrier' isMerge
    cases isMerge
    rfl
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : session ≠ wire := by
        intro isWire
        subst isWire
        exact outside rfl
      show twoPendingAt session = afterCoalesce.inFlight () session
      rw [twoPendingAt_off notWire, afterCoalesce_off notWire]
    | _ => rfl

/-- The carrier really is in flight afterwards, and the source really is ended. -/
theorem the_merge_happened :
    (afterCoalesce.inFlight () wire).Outstanding carrier ∧
      (afterCoalesce.inFlight () wire).resolution escrowed = some (.coalesced carrier) := by
  rw [afterCoalesce_wire]
  exact ⟨⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    merged_other carrier_ne_escrowed⟩, merged_first⟩

end Grass.Process.Tests.Close
