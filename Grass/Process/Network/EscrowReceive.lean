import Grass.Process.Network.Escrow

/-! Logical construction of a ledger after receiving one outstanding occurrence.
Only that occurrence's resolution changes; creation, rank and cancellation
requests are retained. Classical equality makes this a noncomputable logical
producer. It does not execute a runtime receive or establish a live receiver,
session validity or handler admission; those remain network-transition laws. -/

namespace Grass.Process.EscrowLedger

universe u s
variable {Occurrence : Type u} {Session : Type s}

noncomputable section

open Classical

/-- Construct the received ledger for an actual outstanding occurrence. -/
noncomputable def receiveUpdate (ledger : EscrowLedger Occurrence Session) (occurrence : Occurrence)
    (outstanding : ledger.Outstanding occurrence) : EscrowLedger Occurrence Session where
  created := ledger.created
  rank := ledger.rank
  rankOrdersCreated := ledger.rankOrdersCreated
  resolution other := if other = occurrence then some .received else ledger.resolution other
  noFabrication := by
    intro other resolved
    by_cases same : other = occurrence
    · subst other
      exact outstanding.1
    · apply ledger.noFabrication other
      simpa [same] using resolved
  coalesceCarrierLater := by
    intro other carrier merged
    by_cases same : other = occurrence
    · subst other
      simp at merged
    · exact ledger.coalesceCarrierLater other carrier (by simpa [same] using merged)
  cancelRequested := ledger.cancelRequested
  acknowledgedWasRequested := by
    intro other reason acknowledged
    by_cases same : other = occurrence
    · subst other
      simp at acknowledged
    · exact ledger.acknowledgedWasRequested other reason (by simpa [same] using acknowledged)

/-- The selected occurrence is recorded as received. -/
@[simp] theorem receiveUpdate_resolution_self (ledger : EscrowLedger Occurrence Session)
    (occurrence : Occurrence) (outstanding : ledger.Outstanding occurrence) :
    (receiveUpdate ledger occurrence outstanding).resolution occurrence = some .received := by
  simp [receiveUpdate]

/-- Every other occurrence retains its exact previous resolution. -/
theorem receiveUpdate_resolution_other (ledger : EscrowLedger Occurrence Session)
    (occurrence : Occurrence) (outstanding : ledger.Outstanding occurrence)
    {other : Occurrence} (different : other ≠ occurrence) :
    (receiveUpdate ledger occurrence outstanding).resolution other = ledger.resolution other := by
  simp [receiveUpdate, different]

/-- Receiving preserves prior creations, resolutions and cancellation requests. -/
theorem receiveUpdate_extends (ledger : EscrowLedger Occurrence Session)
    (occurrence : Occurrence) (outstanding : ledger.Outstanding occurrence) :
    LedgerExtends ledger (receiveUpdate ledger occurrence outstanding) where
  createdPrefix := List.prefix_refl _
  resolutionPermanent := by
    intro other resolution resolved
    by_cases same : other = occurrence
    · subst other
      exact absurd resolved (by simp [outstanding.2])
    · simpa [receiveUpdate, same] using resolved
  cancelRequestMonotone := by
    intro other requested
    exact requested

/-- No occurrence other than the selected one is resolved by this update. -/
theorem receiveUpdate_resolves_nothing_else (ledger : EscrowLedger Occurrence Session)
    (occurrence : Occurrence) (outstanding : ledger.Outstanding occurrence) :
    ResolvesNothingElse ledger (receiveUpdate ledger occurrence outstanding) occurrence := by
  intro other different
  exact receiveUpdate_resolution_other ledger occurrence outstanding different

/-- Receiving introduces no new escrow occurrence. -/
theorem receiveUpdate_creates_nothing (ledger : EscrowLedger Occurrence Session)
    (occurrence : Occurrence) (outstanding : ledger.Outstanding occurrence) :
    CreatesNothing ledger (receiveUpdate ledger occurrence outstanding) := rfl

/-- Receiving leaves every cancellation-request flag unchanged. -/
theorem receiveUpdate_requests_nothing (ledger : EscrowLedger Occurrence Session)
    (occurrence : Occurrence) (outstanding : ledger.Outstanding occurrence) :
    RequestsNothing ledger (receiveUpdate ledger occurrence outstanding) := by
  intro other
  rfl

end

end Grass.Process.EscrowLedger
