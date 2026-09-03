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
  nowResolved := by rw [afterFullClose_wire]; exact bothClosed_first
  closesEverything := by
    intro other outstanding
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
  have ended := closes.closesEverything stranded both_are_outstanding.2
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

end Grass.Process.Tests.Close
