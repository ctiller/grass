import Grass.Process.Network.WellFormedness
import Tests.Process.TransitionFixtures

/-!
# One nominal, two entries, and what that costs

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.115 and the eighth clause of
`LogicalProcessNetworkCore.WellFormed`.

`EscrowLedger.rankOrdersCreated`'s docstring used to claim this world was
impossible — "an occurrence escrowed twice would be a fabricated identity, and
here it would need a rank strictly below itself". It is not. `created` holds an
`EdgeOccurrence`, which is a *pair* of a message and a `MessageOccurrence`, and
`docs/PROCESS.md` §3 says the occurrence "carries only its nominal identity". So
two entries under one nominal with *different messages* are distinct pairs, and
`rank` is free to order them: `aliasedLedger` ranks them by their payloads.

What the alias costs is stated here rather than described.
`EscrowLedger.atMostOneRecordedEnding` and `outstanding_xor_settled` are keyed on
the pair, while §3's affine `ResolveToken occurrence.id` is keyed on the
identity — so `dropOneOfThem` is a ledger in which one nominal is simultaneously
`.dropped` and `Outstanding`, and every field of `EscrowLedger` is discharged.

The three theorems this file exists for are `aliasedLedger_breaks_the_token`,
`aliased_is_not_wellFormed` and `identitiesDistinct_is_what_refuses_it`. The last
matters most: it is the *clause* that refuses this world, not the transition
family. `SendsEscrow.identityIsFresh` stops a run from reaching it, and §10.109
is the lesson that this is a different theorem from "no well-formed network is
bad" — every result stated over `before.WellFormed` admitted this world as an
input until the clause existed.
-/

namespace Grass.Process.Tests.Identity

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld quiet serverMessage)
open Grass.Process.Tests.Channel (wire)
open Grass.Process.Tests.Transition (serverPlan payload escrowed)

/-! ## The twin -/

/-- A second payload, so the two entries are distinct pairs. -/
def otherPayload : serverMessage () := ⟨9⟩

/--
**A different message under the same nominal.**

`escrowed`'s occurrence identity is `⟨.messageOccurrence, 0⟩` and so is this
one's. What differs is the payload, and that is enough to make the two entries
distinct values of `EdgeOccurrence` — which is exactly the gap.
-/
def twin : EdgeOccurrence serverTopology serverMessage () :=
  ⟨otherPayload, ⟨wire, { id := ⟨.messageOccurrence, 0⟩, isMessage := rfl }⟩⟩

theorem twin_is_not_escrowed : twin ≠ escrowed := by
  intro same
  have payloads := congrArg (fun occurrence => occurrence.1.down) same
  simp [twin, escrowed, Transition.payload, otherPayload] at payloads

/-- **And it carries the same nominal**, which is the whole complaint. -/
theorem twin_shares_the_identity : twin.2.2.id = escrowed.2.2.id := rfl

/-! ## The ledger that holds both -/

open Classical in
/--
Both entries, in flight, ranked by their payloads.

`rank` is where the old docstring's argument was supposed to bite, and it does
not: the two entries are unequal, so nothing forces their ranks to agree, and
ranking by the payload orders them strictly.
-/
noncomputable def aliasedLedger :
    EscrowLedger (EdgeOccurrence serverTopology serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed, twin]
  rank := fun occurrence => occurrence.1.down
  rankOrdersCreated := by
    show ([escrowed, twin].map (fun occurrence => occurrence.1.down)).Pairwise (· < ·)
    simp [escrowed, twin, Transition.payload, otherPayload]
  resolution := fun _ => none
  noFabrication := by simp
  coalesceCarrierLater := by simp
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by simp

open Classical in
/-- And the same ledger with one of the two dropped. -/
noncomputable def dropOneOfThem :
    EscrowLedger (EdgeOccurrence serverTopology serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed, twin]
  rank := fun occurrence => occurrence.1.down
  rankOrdersCreated := by
    show ([escrowed, twin].map (fun occurrence => occurrence.1.down)).Pairwise (· < ·)
    simp [escrowed, twin, Transition.payload, otherPayload]
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
/--
**One nominal, dropped and outstanding at once**, with every field of
`EscrowLedger` discharged.

`atMostOneRecordedEnding` and `outstanding_xor_settled` are keyed on the *pair*,
so they see two occurrences and are satisfied. §3's affine `ResolveToken
occurrence.id` is keyed on the *identity*, and there is one identity here with
two fates. That is the cost the eighth clause exists to refuse.
-/
theorem aliasedLedger_breaks_the_token :
    dropOneOfThem.resolution escrowed = some .dropped ∧
      dropOneOfThem.Outstanding twin ∧ twin.2.2.id = escrowed.2.2.id := by
  refine ⟨?_, ⟨?_, ?_⟩, rfl⟩
  · show (if escrowed = escrowed then some ChannelResolution.dropped else none)
      = some .dropped
    rw [if_pos rfl]
  · show twin ∈ [escrowed, twin]
    simp
  · show (if twin = escrowed then some ChannelResolution.dropped else none) = none
    rw [if_neg twin_is_not_escrowed]

/-! ## The world, and the clause that refuses it -/

open Classical in
/-- `quiet` with both entries on the wire. -/
noncomputable def aliased : ServerWorld :=
  { quiet with
      inFlight := fun _ session => if session = wire then aliasedLedger else EscrowLedger.empty }

open Classical in
theorem aliased_wire : aliased.inFlight () wire = aliasedLedger := by
  show (if wire = wire then aliasedLedger else EscrowLedger.empty) = aliasedLedger
  rw [if_pos rfl]

/--
**The eighth clause refuses it**, which is what a falsifying fixture is for: a
clause nothing can fail is a clause that says nothing.
-/
theorem identitiesDistinct_is_what_refuses_it : ¬ aliased.IdentitiesDistinct := by
  intro distinct
  refine twin_is_not_escrowed (distinct () wire twin escrowed ?_ ?_ rfl)
  · show twin ∈ (aliased.inFlight () wire).created
    rw [aliased_wire]
    show twin ∈ [escrowed, twin]
    simp
  · show escrowed ∈ (aliased.inFlight () wire).created
    rw [aliased_wire]
    show escrowed ∈ [escrowed, twin]
    simp

/-- **So the world is not well formed.** -/
theorem aliased_is_not_wellFormed : ¬ aliased.WellFormed :=
  fun wellFormed => identitiesDistinct_is_what_refuses_it wellFormed.identitiesDistinct

open Classical in
/--
**And no other clause refuses it**, which is why this one had to
be added rather than derived.

Only `occurrencesOnTheirSession` is even about the escrow ledger, and it is
satisfied: both entries name `wire`, which is the session holding them. A reader
who suspects the new clause is implied by the old ones can check this instead of
taking the claim on trust.
-/
theorem the_seventh_clause_is_satisfied : aliased.OccurrencesOnTheirSession := by
  intro edge session occurrence held
  by_cases isWire : session = wire
  · subst isWire
    rw [aliased_wire] at held
    have two : occurrence ∈ [escrowed, twin] := held
    rcases List.mem_cons.mp two with isFirst | rest
    · rw [isFirst]; rfl
    · rw [List.mem_singleton.mp rest]; rfl
  · refine absurd ?_ (by simp : occurrence ∉ ([] : List _))
    have empty : aliased.inFlight edge session = EscrowLedger.empty := by
      show (if session = wire then aliasedLedger else EscrowLedger.empty)
        = EscrowLedger.empty
      rw [if_neg isWire]
    rw [empty] at held
    exact held

end Grass.Process.Tests.Identity
