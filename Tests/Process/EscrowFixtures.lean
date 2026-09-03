import Grass.Process.Network.Escrow

/-!
# Escrow accounting, at a ledger you can count

`Grass/Process/Network/Escrow.lean` proves its laws over an abstract ledger, and
abstract theorems can be true of nothing. This file exhibits a ledger with
settled, outstanding, coalesced and rerouted occurrences, counts them, and
follows one across an extension.

What it pins that a reader would otherwise take on trust:

* **Requesting cancellation does not reclaim escrow.**
  `cancelled_message_is_still_in_flight` builds an occurrence with a
  cancellation requested against it that is nonetheless outstanding. The module
  says plainly that its own theorem is not the guard — the theorem is a
  projection and would survive a field tying the two together, merely becoming
  vacuous. This ledger is the guard: it stops elaborating the moment such a
  field exists.
* **Coalescing cannot go in circles.** `coalesce_cycle_impossible` is stated
  over an arbitrary ledger, not this one: two occurrences merging into each
  other is unconstructible. An earlier revision of the module forbade only
  self-merging, under which a two-cycle elaborated, satisfied every field, and
  reported itself accounted for while both payloads landed nowhere.
* **Reroute is constructible.** `homeLedger` actually holds a `rerouted`
  occurrence, to a session that is not this one. An earlier revision made
  `rerouted` carry a carrier and demanded it be escrowed *here*, which no
  genuine reroute can satisfy; the fixture that would have caught it did not
  exist, and `Session := Unit` made it unwritable anyway. `Wire` has two values
  for that reason.
* **An acknowledgement acknowledges something.**
  `acknowledgement_needs_a_request` is the teeth of `acknowledgedWasRequested`,
  over an arbitrary ledger.
* **A request does not evaporate.** `cancel_request_survives` follows the
  outstanding request across the extension.

`Slot` and `Wire` are finite so that the counting arguments are `decide`-able
and the fixture argues by computation.
-/

namespace Grass.Process.Tests.Escrow

open Grass.Process
open Grass.Specification

/-- Four message occurrences on the channel under test. -/
inductive Slot
  | first
  | second
  | third
  | fourth
  deriving DecidableEq, Repr

/-- Two sessions, so that a reroute has somewhere to go. -/
inductive Wire
  | home
  | away
  deriving DecidableEq, Repr

/-- The scope this fixture's cancellation point belongs to. -/
def escrowScope : ScopeId := ⟨["Tests", "Process", "Escrow"]⟩

/-- The one declared cancellation point in this fixture. -/
def shutdownPoint : CancelReason := ⟨⟨escrowScope, "shutdown"⟩⟩

/-- Allocation order: exactly the order of `created`. -/
def slotRank : Slot → Nat
  | .first => 0
  | .second => 1
  | .third => 2
  | .fourth => 3

/--
The ledger on the `home` session: `first` was received, `third` merged forward
into `fourth`, `fourth` was rerouted away, and `second` is still in flight with
a cancellation requested against it.
-/
def homeResolution : Slot → Option (ChannelResolution Slot Wire)
  | .first => some .received
  | .third => some (.coalesced .fourth)
  | .fourth => some (.rerouted .away)
  | _ => none

def homeLedger : EscrowLedger Slot Wire where
  created := [.first, .second, .third, .fourth]
  rank := slotRank
  rankOrdersCreated := by decide
  resolution := homeResolution
  noFabrication := by
    intro occurrence resolved
    cases occurrence <;> simp_all [homeResolution]
  coalesceCarrierLater := by
    intro occurrence carrier merged
    cases occurrence <;> simp_all [homeResolution, slotRank] <;>
      (subst merged; decide)
  cancelRequested := fun slot => slot == .second
  acknowledgedWasRequested := by
    intro occurrence reason acknowledged
    cases occurrence <;> simp_all [homeResolution]

/-! ## Accounting, counted -/

/-- Three occurrences have ended. -/
theorem home_settled : homeLedger.settled = [.first, .third, .fourth] := by decide

/-- One is still in flight. -/
theorem home_outstanding : homeLedger.outstanding = [.second] := by decide

/-- And the two add up to what was escrowed. -/
theorem home_accounts :
    homeLedger.settled.length + homeLedger.outstanding.length =
      homeLedger.created.length :=
  homeLedger.accounting

/-- Which, at this ledger, is three and one making four. -/
theorem home_counts :
    homeLedger.settled.length = 3 ∧ homeLedger.outstanding.length = 1 := by
  rw [home_settled, home_outstanding]
  exact ⟨rfl, rfl⟩

/-! ## Reroute is a thing you can build -/

/--
**A rerouted occurrence, to a session that is not this one.**

The positive witness the module's `rerouted` needs and an earlier revision could
not have: with a carrier demanded to be escrowed in *this* ledger, no genuine
reroute was constructible, and with `Session := Unit` no fixture could tell.
-/
theorem fourth_went_away :
    homeLedger.resolution .fourth = some (.rerouted Wire.away) := rfl

/-- It is not a terminal ending: the payload went somewhere. -/
theorem reroute_is_not_terminal :
    ¬ (ChannelResolution.rerouted (Occurrence := Slot) Wire.away).IsTerminal :=
  ChannelResolution.rerouted_not_terminal Wire.away

/-- And the obligation it creates is dischargeable — here, trivially. -/
theorem home_reroutes_land : homeLedger.ReroutedElsewhere (fun _ _ _ => True) := by
  intro _ _ _
  exact ⟨.first, trivial⟩

/-! ## Coalescing cannot go in circles -/

/--
**Two occurrences cannot merge into each other.**

Stated over an arbitrary ledger, because it is a fact about the type. Under the
module's earlier law, which forbade only self-merging, the cycle below
elaborated: every field discharged, the accounting reported the ledger in order,
and two payloads were each "passed on" to the other and landed nowhere.
-/
theorem coalesce_cycle_impossible (ledger : EscrowLedger Slot Wire)
    (left right : Slot)
    (leftMerges : ledger.resolution left = some (.coalesced right))
    (rightMerges : ledger.resolution right = some (.coalesced left)) : False :=
  CoalescesTo.no_cycle
    (CoalescesTo.trans (CoalescesTo.step leftMerges) (CoalescesTo.step rightMerges))

/-- Nor into themselves, which the same rank law gives. -/
theorem coalesce_into_self_impossible (ledger : EscrowLedger Slot Wire)
    (occurrence : Slot)
    (merges : ledger.resolution occurrence = some (.coalesced occurrence)) : False :=
  CoalescesTo.no_cycle (CoalescesTo.step merges)

/-- Nor into an occurrence that was never escrowed. -/
theorem coalesce_into_unescrowed_impossible (ledger : EscrowLedger Slot Wire)
    (occurrence carrier : Slot) (absent : carrier ∉ ledger.created)
    (merges : ledger.resolution occurrence = some (.coalesced carrier)) : False :=
  absent (ledger.coalesceCarrierLater occurrence carrier merges).1

/-! ## Cancellation -/

/--
**The message with a cancellation requested is still in flight.**

`docs/PROCESS.md` §3: "Requesting cancellation does not reclaim escrow." This
ledger says both things about `second` at once, which is only possible because
`cancelRequested` and `resolution` are unrelated fields.
-/
theorem cancelled_message_is_still_in_flight :
    homeLedger.cancelRequested .second = true ∧ homeLedger.Outstanding .second :=
  ⟨rfl, ⟨by decide, rfl⟩⟩

/--
**An acknowledgement acknowledges something.**

The teeth of `acknowledgedWasRequested`, over an arbitrary ledger: an
acknowledgement of a request that was never made is unconstructible.
-/
theorem acknowledgement_needs_a_request (ledger : EscrowLedger Slot Wire)
    (occurrence : Slot) (reason : CancelReason)
    (never : ledger.cancelRequested occurrence = false)
    (acknowledged : ledger.resolution occurrence = some (.cancelAcknowledged reason)) :
    False := by
  rw [ledger.acknowledgedWasRequested occurrence reason acknowledged] at never
  exact absurd never (by simp)

/-! ## Later in the same execution -/

/-- Later: the outstanding request was acknowledged. -/
def laterResolution : Slot → Option (ChannelResolution Slot Wire)
  | .first => some .received
  | .second => some (.cancelAcknowledged shutdownPoint)
  | .third => some (.coalesced .fourth)
  | .fourth => some (.rerouted .away)

def laterLedger : EscrowLedger Slot Wire where
  created := [.first, .second, .third, .fourth]
  rank := slotRank
  rankOrdersCreated := by decide
  resolution := laterResolution
  noFabrication := by
    intro occurrence resolved
    cases occurrence <;> simp_all [laterResolution]
  coalesceCarrierLater := by
    intro occurrence carrier merged
    cases occurrence <;> simp_all [laterResolution, slotRank] <;>
      (subst merged; decide)
  cancelRequested := fun slot => slot == .second
  acknowledgedWasRequested := by
    intro occurrence reason acknowledged
    cases occurrence <;> simp_all [laterResolution]

/-- It is the same execution, later. -/
theorem homeExtends : LedgerExtends homeLedger laterLedger where
  createdPrefix := List.prefix_refl _
  resolutionPermanent := by
    intro occurrence resolution ended
    cases occurrence <;>
      simp_all [homeLedger, laterLedger, homeResolution, laterResolution]
  cancelRequestMonotone := by
    intro occurrence requested
    cases occurrence <;> simp_all [homeLedger, laterLedger]

/--
**The occurrence that was in flight is still accounted for.**

`docs/FOUNDATION.md` law 5 for escrow: `second` did not vanish between the two
ledgers. It ended, by a named resolution, at a named cancellation point.
-/
theorem second_slot_is_accounted_for :
    laterLedger.Outstanding .second ∨ laterLedger.Resolved .second = true :=
  homeExtends.noLoss cancelled_message_is_still_in_flight.2

/-- Specifically, its cancellation was acknowledged at the point it was declared. -/
theorem second_slot_acknowledged :
    laterLedger.resolution .second = some (.cancelAcknowledged shutdownPoint) := rfl

/-- The request did not evaporate on the way there. -/
theorem cancel_request_survives : laterLedger.cancelRequested .second = true :=
  homeExtends.cancelRequestMonotone .second rfl

/-- What was already ended stays ended, with the same ending. -/
theorem first_slot_ending_is_permanent :
    laterLedger.resolution .first = some .received :=
  homeExtends.resolvedStaysResolved (resolution := .received) rfl

/-- **And the prefix half of conservation: what was settled stays settled.** -/
theorem settled_slots_stay_settled :
    Slot.first ∈ laterLedger.settled ∧ Slot.third ∈ laterLedger.settled := by
  refine ⟨homeExtends.settled_monotone ?_, homeExtends.settled_monotone ?_⟩ <;> decide

end Grass.Process.Tests.Escrow
