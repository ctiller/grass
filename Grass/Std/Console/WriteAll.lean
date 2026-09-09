import Grass.Std.Logical.Vec

/-!
# Pure bounded write-all cursor

This module describes the arithmetic at the center of a write-all loop.  It has
no provider or execution semantics. `WriteResponse` is a semantic response
carrying an emitted-prefix witness. A future platform refinement must justify
that witness from physical output history; an API return alone need not supply
it. A machine consumer decides when to call `respond`.
-/

namespace Grass.Std.Console

open Logical

/-- The terminal result of a write-all attempt. -/
inductive WriteOutcome where
  | success
  | writeFailed
  | noProgress
deriving DecidableEq, Repr

/-- A position in `payload`, carrying the invariant that it is in bounds. -/
structure WriteCursor (payload : Vec Byte) where
  committed : Nat
  within : committed ≤ payload.length

/-- The suffix beyond the semantically committed prefix. -/
def WriteCursor.remaining {payload : Vec Byte} (cursor : WriteCursor payload) : Vec Byte :=
  payload.drop cursor.committed

/-- A semantic emitted-byte count bounded by the request at `cursor`.
On failure this is a ghost witness, not a promised API-visible return value. -/
structure WriteCount {payload : Vec Byte} (cursor : WriteCursor payload) where
  value : Nat
  within : value ≤ cursor.remaining.length

/-- A semantic response and its emitted-prefix witness, not a raw API response. -/
inductive WriteResponse {payload : Vec Byte} (cursor : WriteCursor payload) where
  | success (count : WriteCount cursor)
  | failure (count : WriteCount cursor)

/-- Either another bounded request position or a terminal result and position. -/
inductive WriteNext (payload : Vec Byte) where
  | retry (cursor : WriteCursor payload)
  | done (outcome : WriteOutcome) (cursor : WriteCursor payload)

/-- Recover the cursor from either continuation shape. -/
def WriteNext.cursor {payload : Vec Byte} (next : WriteNext payload) : WriteCursor payload :=
  match next with
  | .retry cursor | .done _ cursor => cursor

/-- Recover the bounded count from either semantic response. -/
def WriteResponse.count {payload : Vec Byte} {cursor : WriteCursor payload}
    (response : WriteResponse cursor) : WriteCount cursor :=
  match response with
  | .success count | .failure count => count

/-- Move the semantic cursor by its bounded emitted-byte count. -/
def advance {payload : Vec Byte} (cursor : WriteCursor payload)
    (count : WriteCount cursor) : WriteCursor payload where
  committed := cursor.committed + count.value
  within := by
    have bounded := count.within
    have cursorWithin := cursor.within
    simp only [WriteCursor.remaining, Vec.length_drop] at bounded
    omega

/-- Interpret a response while work remains.

A successful zero count is terminal `noProgress`.  A positive partial count is
retried, and completion is terminal success.  Failure is terminal after
retaining every byte witnessed as emitted, including a possible full suffix.
-/
def respond {payload : Vec Byte} (cursor : WriteCursor payload)
    (_nonempty : cursor.committed < payload.length)
    (response : WriteResponse cursor) : WriteNext payload :=
  match response with
  | .success count =>
      if count.value = 0 then
        .done .noProgress cursor
      else
        let next := advance cursor count
        if next.committed = payload.length then
          .done .success next
        else
          .retry next
  | .failure count => .done .writeFailed (advance cursor count)

/-- At every cursor, the committed prefix and derived suffix reconstruct the
original payload. -/
theorem prefix_suffix_conservation {payload : Vec Byte} (cursor : WriteCursor payload) :
    payload.take cursor.committed ++ cursor.remaining = payload := by
  exact Vec.append_splitAt payload cursor.committed

/-- Advancing commits exactly the next prefix of the previous suffix. -/
theorem advance_prefix_exact {payload : Vec Byte} (cursor : WriteCursor payload)
    (count : WriteCount cursor) :
    payload.take (advance cursor count).committed =
      payload.take cursor.committed ++ cursor.remaining.take count.value := by
  exact Vec.take_add payload cursor.committed count.value

/-- The bytes attributed to either response are exactly the next bounded prefix. -/
def WriteResponse.emitted {payload : Vec Byte} {cursor : WriteCursor payload}
    (response : WriteResponse cursor) : Vec Byte :=
  match response with
  | .success count | .failure count => cursor.remaining.take count.value

/-- Both response branches extend the committed prefix by precisely `emitted`. -/
theorem response_emitted_exact {payload : Vec Byte} (cursor : WriteCursor payload)
    (response : WriteResponse cursor) :
    payload.take
        (match response with
         | .success count | .failure count => (advance cursor count).committed) =
      payload.take cursor.committed ++ response.emitted := by
  cases response with
  | success count => exact advance_prefix_exact cursor count
  | failure count => exact advance_prefix_exact cursor count

/-- `respond_prefix_exact` preserves the exact-prefix equation, including
the zero-progress branch whose emitted segment is empty. -/
theorem respond_prefix_exact {payload : Vec Byte} (cursor : WriteCursor payload)
    (nonempty : cursor.committed < payload.length) (response : WriteResponse cursor) :
    payload.take (respond cursor nonempty response).cursor.committed =
      payload.take cursor.committed ++ response.emitted := by
  cases response with
  | failure count => exact advance_prefix_exact cursor count
  | success count =>
      simp only [respond]
      split <;> rename_i hzero
      · simp [WriteNext.cursor, WriteResponse.emitted, hzero]
      · split <;> exact advance_prefix_exact cursor count

/-- Every retry produced by `respond` strictly decreases the remaining length. -/
theorem respond_retry_decreases {payload : Vec Byte} (cursor : WriteCursor payload)
    (nonempty : cursor.committed < payload.length) (response : WriteResponse cursor)
    (next : WriteCursor payload) (hretry : respond cursor nonempty response = .retry next) :
    next.remaining.length < cursor.remaining.length := by
  cases response with
  | failure count => simp [respond] at hretry
  | success count =>
      simp only [respond] at hretry
      split at hretry
      · simp at hretry
      · split at hretry
        · simp at hretry
        · cases hretry
          exact Vec.length_drop_lt_of_pos payload (Nat.pos_of_ne_zero ‹count.value ≠ 0›) nonempty

/-- Terminal success can only occur at the end of the payload. -/
theorem respond_success_complete {payload : Vec Byte} (cursor : WriteCursor payload)
    (nonempty : cursor.committed < payload.length) (response : WriteResponse cursor)
    (next : WriteCursor payload)
    (hdone : respond cursor nonempty response = .done .success next) :
    next.committed = payload.length := by
  cases response with
  | failure count => simp [respond] at hdone
  | success count =>
      simp only [respond] at hdone
      split at hdone
      · simp at hdone
      · split at hdone
        · cases hdone
          assumption
        · simp at hdone

/-- `respond_noProgress_unchanged` preserves the proper committed prefix. -/
theorem respond_noProgress_unchanged {payload : Vec Byte} (cursor : WriteCursor payload)
    (nonempty : cursor.committed < payload.length) (response : WriteResponse cursor)
    (next : WriteCursor payload)
    (hdone : respond cursor nonempty response = .done .noProgress next) :
    next = cursor ∧ next.committed < payload.length := by
  cases response with
  | failure count => simp [respond] at hdone
  | success count =>
      simp only [respond] at hdone
      split at hdone
      · cases hdone
        exact ⟨rfl, nonempty⟩
      · split at hdone <;> simp at hdone

/-- Failure retains the bounded count without imposing positivity or excluding a
count equal to the entire remaining suffix. -/
theorem respond_failure_advances {payload : Vec Byte} (cursor : WriteCursor payload)
    (nonempty : cursor.committed < payload.length) (count : WriteCount cursor) :
    respond cursor nonempty (.failure count) =
      .done .writeFailed (advance cursor count) := rfl

/-- The maximum admissible response count covers the entire remaining suffix. -/
def fullRemainingCount {payload : Vec Byte} (cursor : WriteCursor payload) : WriteCount cursor where
  value := cursor.remaining.length
  within := Nat.le_refl _

/-- A failure may emit the entire remaining suffix, and then its terminal
cursor is exactly complete. -/
theorem respond_failure_may_commit_all {payload : Vec Byte} (cursor : WriteCursor payload)
    (nonempty : cursor.committed < payload.length) :
    (respond cursor nonempty (.failure (fullRemainingCount cursor))).cursor.committed =
      payload.length := by
  simp [respond, WriteNext.cursor, advance, fullRemainingCount, WriteCursor.remaining,
    Vec.length_drop, Nat.add_sub_of_le cursor.within]

end Grass.Std.Console
