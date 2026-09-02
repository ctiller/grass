import Grass.Process.Network.Escrow

/-!
# Escrow conservation, at a ledger you can count

`Grass/Process/Network/Escrow.lean` proves conservation, at-most-one resolution
and no-loss over an abstract ledger. Abstract theorems can be true of nothing,
so this file exhibits a ledger with both settled and outstanding entries, and
counts them.

It also pins the three claims the module makes that a reader would otherwise
have to take on trust:

* **Requesting cancellation does not reclaim escrow.**
  `cancelled_message_is_still_in_flight` builds an occurrence with a
  cancellation requested that is nonetheless outstanding. If a future field ever
  tied `cancelRequested` to `resolution`, this ledger would stop elaborating.
* **A replacement must exist and must be a different occurrence.**
  `coalesce_into_unescrowed_impossible` and `coalesce_into_self_impossible` are
  the teeth of `replacementEscrowed`: without it, `coalesced` and `rerouted`
  would be drops wearing a hat, which is `docs/FOUNDATION.md` law 5.
* **No loss across an extension.** `second_slot_is_accounted_for` follows one
  occurrence from in-flight to timed-out and shows it is still accounted for.

`Slot` is a four-element occurrence type so that every law here is `decide`-able
and the fixture argues by computation rather than by tactic.
-/

namespace Grass.Process.Tests.Escrow

open Grass.Process

/-- Four message occurrences, so the laws are decidable. -/
inductive Slot
  | first
  | second
  | third
  | fourth
  deriving DecidableEq, Repr

/-- One session; this fixture is about escrow, not routing. -/
abbrev Session := Unit

/--
The ledger: `first` was received, `third` merged into `second`, and `second` is
still in flight with a cancellation requested against it.
-/
def sampleResolution : Slot → Option (ChannelResolution Slot Session)
  | .first => some .received
  | .third => some (.coalesced .second)
  | _ => none

def sample : EscrowLedger Slot Session where
  created := [.first, .second, .third]
  createdDistinct := by decide
  resolution := sampleResolution
  noFabrication := by
    intro occurrence resolved
    cases occurrence <;> simp_all [sampleResolution]
  cancelRequested := fun slot => slot == .second
  replacementEscrowed := by
    intro occurrence carrier carried
    cases occurrence <;>
      simp_all [sampleResolution, ChannelResolution.replacement] <;>
      (subst carried; decide)

/-! ## Conservation, counted -/

/-- Two occurrences have ended. -/
theorem sample_settled : sample.settled = [.first, .third] := by decide

/-- One is still in flight. -/
theorem sample_outstanding : sample.outstanding = [.second] := by decide

/--
And the two add up to what was escrowed.

`EscrowLedger.conservation` proves this in general; this instance shows the
general statement is not about the empty ledger.
-/
theorem sample_conserves :
    sample.settled.length + sample.outstanding.length = sample.created.length :=
  sample.conservation

/-- Which, at this ledger, is two and one making three. -/
theorem sample_counts : sample.settled.length = 2 ∧ sample.outstanding.length = 1 := by
  rw [sample_settled, sample_outstanding]
  exact ⟨rfl, rfl⟩

/-! ## Requesting cancellation does not reclaim escrow -/

/--
**The message with a cancellation requested is still in flight.**

`docs/PROCESS.md` §3: "Requesting cancellation does not reclaim escrow." The
ledger says both things about `second` at once, which is only possible because
`cancelRequested` and `resolution` are unrelated fields.
-/
theorem cancelled_message_is_still_in_flight :
    sample.cancelRequested .second = true ∧ sample.Outstanding .second := by
  refine ⟨rfl, ⟨by decide, rfl⟩⟩

/-- And the general theorem applies to it. -/
theorem cancelled_second_escrow_intact : sample.resolution .second = none :=
  sample.cancel_request_leaves_escrow .second cancelled_message_is_still_in_flight.2
    cancelled_message_is_still_in_flight.1

/-! ## A replacement is not an escape hatch -/

/--
**Coalescing into an occurrence that was never escrowed is impossible.**

The teeth of `replacementEscrowed`. Without it a channel could report that a
message had merged into something that does not exist, and the payload would be
gone while the ledger claimed it had been passed on.

Stated over an arbitrary ledger, not just `sample`, because the property is a
fact about the type rather than about this fixture.
-/
theorem coalesce_into_unescrowed_impossible (ledger : EscrowLedger Slot Session)
    (occurrence carrier : Slot) (absent : carrier ∉ ledger.created)
    (claim : ledger.resolution occurrence = some (.coalesced carrier)) : False :=
  absent (ledger.replacementEscrowed occurrence carrier (by rw [claim]; rfl)).1

/-- And an occurrence cannot merge into itself, which would be a silent drop. -/
theorem coalesce_into_self_impossible (ledger : EscrowLedger Slot Session)
    (occurrence : Slot)
    (claim : ledger.resolution occurrence = some (.coalesced occurrence)) : False :=
  (ledger.replacementEscrowed occurrence occurrence (by rw [claim]; rfl)).2 rfl

/-- The same for reroute, which carries a replacement for the same reason. -/
theorem reroute_into_self_impossible (ledger : EscrowLedger Slot Session)
    (occurrence : Slot) (destination : Session)
    (claim : ledger.resolution occurrence = some (.rerouted destination occurrence)) :
    False :=
  (ledger.replacementEscrowed occurrence occurrence (by rw [claim]; rfl)).2 rfl

/-! ## No loss across an extension -/

/-- Later: `fourth` was escrowed, and `second` timed out. -/
def laterResolution : Slot → Option (ChannelResolution Slot Session)
  | .first => some .received
  | .second => some .timedOut
  | .third => some (.coalesced .second)
  | .fourth => none

def later : EscrowLedger Slot Session where
  created := [.first, .second, .third, .fourth]
  createdDistinct := by decide
  resolution := laterResolution
  noFabrication := by
    intro occurrence resolved
    cases occurrence <;> simp_all [laterResolution]
  cancelRequested := fun slot => slot == .second
  replacementEscrowed := by
    intro occurrence carrier carried
    cases occurrence <;>
      simp_all [laterResolution, ChannelResolution.replacement] <;>
      (subst carried; decide)

/-- It is the same execution, later. -/
theorem sampleExtends : LedgerExtends sample later where
  createdPrefix := ⟨[.fourth], rfl⟩
  resolutionPermanent := by
    intro occurrence resolution ended
    cases occurrence <;> simp_all [sample, later, sampleResolution, laterResolution]

/--
**The occurrence that was in flight is still accounted for.**

`docs/FOUNDATION.md` law 5 for escrow: `second` did not vanish between the two
ledgers. It ended, by a named resolution.
-/
theorem second_slot_is_accounted_for :
    later.Outstanding .second ∨ later.Resolved .second = true :=
  sampleExtends.noLoss cancelled_message_is_still_in_flight.2

/-- Specifically, it timed out — and the ending is the one the ledger records. -/
theorem second_slot_timed_out : later.resolution .second = some .timedOut := rfl

/-- What was already ended stays ended, with the same ending. -/
theorem first_slot_ending_is_permanent :
    later.resolution .first = some .received :=
  sampleExtends.resolvedStaysResolved (resolution := .received) rfl

/-- And the later ledger conserves too, with one more escrowed and one fewer live. -/
theorem later_conserves : later.settled = [.first, .second, .third] ∧
    later.outstanding = [.fourth] := by
  refine ⟨by decide, by decide⟩

end Grass.Process.Tests.Escrow
