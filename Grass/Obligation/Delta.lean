import Grass.Obligation.Core

/-!
# Ledger deltas

`docs/OBLIGATIONS.md` §2: "Every semantic transition states how it transforms the
ledger. It may preserve, create, discharge, split, join, or transfer obligations
only through the owning protocol theorem. Dropping, duplicating, or fabricating
obligations is forbidden."

Six operations are named there but only five are constructors below, and the
omission is the design. **Preservation is not a delta.** An obligation a
transition does not mention is preserved, by framing, and there is no way to
write down "preserve" as an action. Had `preserve` been a constructor, a
transition could list a preserve for an obligation it also discharged, and the
ledger law would have to rule that out; with framing, the situation is
unspellable.

`consumes` and `produces` project the identities a delta destroys and creates.
The M5 ledger law is stated over these projections: no identity is consumed
twice, no identity is produced that was already live, and no live identity
vanishes without appearing in some `consumes`. This module supplies the
vocabulary and the projections, not those theorems.
-/

namespace Grass.Obligation

open Grass.Core

/--
One change a transition makes to the obligation ledger.

An obligation not named by any delta of a transition is preserved unchanged.
-/
inductive LedgerDelta : Type 1 where
  /-- A protocol created a new obligation. -/
  | create (obligation : Obligation)
  /-- The required action occurred and this obligation ends. -/
  | discharge (obligation : ObligationId)
  /-- One obligation becomes several, together covering the same duty. -/
  | split (source : ObligationId) (into : List Obligation)
  /-- Several obligations become one. -/
  | join (sources : List ObligationId) (into : Obligation)
  /-- Responsibility moves to another context; the duty itself is unchanged. -/
  | transfer (obligation : ObligationId) (newOwner : ContextId)

namespace LedgerDelta

/--
The identities this delta removes from the ledger.

A transfer consumes nothing: `docs/OBLIGATIONS.md` §1 makes transfer a change of
owner, not an end of the duty, and the identity survives it.
-/
def consumes : LedgerDelta → List ObligationId
  | .create _ => []
  | .discharge id => [id]
  | .split source _ => [source]
  | .join sources _ => sources
  | .transfer _ _ => []

/-- The identities this delta adds to the ledger. -/
def produces : LedgerDelta → List ObligationId
  | .create obligation => [obligation.id]
  | .discharge _ => []
  | .split _ into => into.map Obligation.id
  | .join _ into => [into.id]
  | .transfer _ _ => []

/--
`delta.PreservesIdentity id` holds when `delta` leaves `id` exactly where it was.

This is the framing predicate the M5 ledger law uses to justify not mentioning
an obligation: an untouched obligation is preserved because no delta consumed or
produced it.
-/
def PreservesIdentity (delta : LedgerDelta) (id : ObligationId) : Prop :=
  id ∉ delta.consumes ∧ id ∉ delta.produces

instance (delta : LedgerDelta) (id : ObligationId) : Decidable (delta.PreservesIdentity id) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem consumes_transfer (id : ObligationId) (owner : ContextId) :
    (LedgerDelta.transfer id owner).consumes = [] := rfl

@[simp] theorem produces_transfer (id : ObligationId) (owner : ContextId) :
    (LedgerDelta.transfer id owner).produces = [] := rfl

@[simp] theorem consumes_create (obligation : Obligation) :
    (LedgerDelta.create obligation).consumes = [] := rfl

@[simp] theorem produces_create (obligation : Obligation) :
    (LedgerDelta.create obligation).produces = [obligation.id] := rfl

@[simp] theorem consumes_discharge (id : ObligationId) :
    (LedgerDelta.discharge id).consumes = [id] := rfl

@[simp] theorem produces_discharge (id : ObligationId) :
    (LedgerDelta.discharge id).produces = [] := rfl

/--
A transfer preserves every identity, including the one it moves.

This is worth stating because it is the fact that distinguishes transfer from
discharge-and-recreate: `docs/OBLIGATIONS.md` §3 lets a terminal edge report
`transferred` only when "a named live owner accepted it", and a transfer that
minted a new identity would break the correspondence between the obligation that
was created and the one that was accepted.
-/
theorem preservesIdentity_transfer (moved : ObligationId) (owner : ContextId)
    (id : ObligationId) : (LedgerDelta.transfer moved owner).PreservesIdentity id :=
  ⟨by simp, by simp⟩

/-- A discharge consumes exactly the obligation it names and no other. -/
theorem preservesIdentity_discharge_of_ne {discharged id : ObligationId}
    (h : id ≠ discharged) : (LedgerDelta.discharge discharged).PreservesIdentity id :=
  ⟨by simp [h], by simp⟩

end LedgerDelta

/--
The complete ledger effect of one transition.

A list rather than a single delta, because one transition may discharge one
obligation while creating another — an ABI call returning while creating a
completion obligation, for example.
-/
abbrev LedgerEffect := List LedgerDelta

namespace LedgerEffect

/-- Every identity this effect removes. -/
def consumes (effect : LedgerEffect) : List ObligationId :=
  effect.flatMap LedgerDelta.consumes

/-- Every identity this effect adds. -/
def produces (effect : LedgerEffect) : List ObligationId :=
  effect.flatMap LedgerDelta.produces

/-- `effect.PreservesIdentity id` holds when no delta of `effect` touches `id`. -/
def PreservesIdentity (effect : LedgerEffect) (id : ObligationId) : Prop :=
  ∀ delta ∈ effect, delta.PreservesIdentity id

/-- The empty effect changes nothing, which is the framing base case. -/
@[simp] theorem preservesIdentity_nil (id : ObligationId) :
    PreservesIdentity [] id := by simp [PreservesIdentity]

@[simp] theorem consumes_nil : consumes [] = [] := rfl

@[simp] theorem produces_nil : produces [] = [] := rfl

end LedgerEffect

end Grass.Obligation
