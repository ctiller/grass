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
inductive LedgerDelta where
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
deriving DecidableEq, Repr

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
The identities this delta leaves in place but reassigns to another owner.

Separate from `consumes` and `produces` because a transfer does neither: the duty
survives with its identity intact. It is nonetheless a change to that
obligation's row in the ledger, which is why `PreservesIdentity` has to see it.
-/
def reowns : LedgerDelta → List ObligationId
  | .transfer id _ => [id]
  | .create _ | .discharge _ | .split _ _ | .join _ _ => []

/--
`delta.PreservesIdentity id` holds when `delta` leaves `id` exactly as it was.

This is the framing predicate the M5 ledger law uses to justify not mentioning an
obligation. It must therefore mean *untouched*, and an earlier version did not:
it checked only `consumes` and `produces`, so it held for the very obligation a
transfer had just re-owned. Any frame rule of the form
`PreservesIdentity id → ledger[id] unchanged` would have been false at exactly
the transfers `docs/OBLIGATIONS.md` §1 cares most about.
-/
def PreservesIdentity (delta : LedgerDelta) (id : ObligationId) : Prop :=
  id ∉ delta.consumes ∧ id ∉ delta.produces ∧ id ∉ delta.reowns

instance (delta : LedgerDelta) (id : ObligationId) : Decidable (delta.PreservesIdentity id) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/--
`delta.WellFormed` rules out the deltas that would drop or fabricate a duty.

`docs/OBLIGATIONS.md` §2: "Dropping, duplicating, or fabricating obligations is
forbidden", and `docs/FOUNDATION.md` law 7 is the same rule stated as no
obligation disappearance. Two constructors can express a violation on their own,
and this is what closes them:

- `split source []` consumes an obligation and produces nothing, destroying a
  duty without discharging it;
- `join [] into` produces an obligation from no sources, inventing one.

The `Nodup` conditions close the duplication half: a split that produced the same
identity twice, or a join that consumed one twice, would let a single duty be
counted as two.
-/
def WellFormed : LedgerDelta → Prop
  | .create _ => True
  | .discharge _ => True
  | .split _ into => into ≠ [] ∧ (into.map Obligation.id).Nodup
  | .join sources _ => sources ≠ [] ∧ sources.Nodup
  | .transfer _ _ => True

instance : (delta : LedgerDelta) → Decidable delta.WellFormed
  | .create _ => .isTrue trivial
  | .discharge _ => .isTrue trivial
  | .split _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .join _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .transfer _ _ => .isTrue trivial

@[simp] theorem wellFormed_create (obligation : Obligation) :
    (LedgerDelta.create obligation).WellFormed := trivial

@[simp] theorem wellFormed_discharge (id : ObligationId) :
    (LedgerDelta.discharge id).WellFormed := trivial

@[simp] theorem wellFormed_transfer (id : ObligationId) (owner : ContextId) :
    (LedgerDelta.transfer id owner).WellFormed := trivial

/-- A split into nothing is not a split; it is a disappearance. -/
theorem not_wellFormed_split_nil (source : ObligationId) :
    ¬ (LedgerDelta.split source []).WellFormed := fun h => h.1 rfl

/-- A join from nothing is not a join; it is a fabrication. -/
theorem not_wellFormed_join_nil (into : Obligation) :
    ¬ (LedgerDelta.join [] into).WellFormed := fun h => h.1 rfl

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
A transfer leaves every *other* identity alone.

Note the `h`. The obligation being moved is emphatically not preserved: its owner
changes, which is the whole content of a transfer. An earlier version of this
theorem quantified over all `id`, which made `PreservesIdentity` useless as a
frame rule precisely where transfers occur.

What a transfer does preserve about the moved obligation is its *identity*, and
that is `identity_survives_transfer` below. `docs/OBLIGATIONS.md` §3 lets a
terminal edge report `transferred` only when "a named live owner accepted it", so
the correspondence between the obligation created and the one accepted has to
survive; a transfer that minted a new identity would break it.
-/
theorem preservesIdentity_transfer_of_ne {moved id : ObligationId} (h : id ≠ moved)
    (owner : ContextId) : (LedgerDelta.transfer moved owner).PreservesIdentity id :=
  ⟨by simp, by simp, by simp [reowns, h]⟩

/-- The moved obligation is not preserved: a transfer is a change to its row. -/
theorem not_preservesIdentity_transfer_self (moved : ObligationId) (owner : ContextId) :
    ¬ (LedgerDelta.transfer moved owner).PreservesIdentity moved := by
  rintro ⟨_, _, hr⟩
  exact hr (by simp [reowns])

/-- A transfer neither consumes nor produces, so the duty's identity survives it.
This is what distinguishes transfer from discharge-and-recreate. -/
theorem identity_survives_transfer (moved : ObligationId) (owner : ContextId) :
    (LedgerDelta.transfer moved owner).consumes = [] ∧
      (LedgerDelta.transfer moved owner).produces = [] := ⟨rfl, rfl⟩

/-- A discharge consumes exactly the obligation it names and no other. -/
theorem preservesIdentity_discharge_of_ne {discharged id : ObligationId}
    (h : id ≠ discharged) : (LedgerDelta.discharge discharged).PreservesIdentity id :=
  ⟨by simp [h], by simp, by simp [reowns]⟩

/--
`Applicable live effect` holds when `effect` can lawfully act on a ledger whose
live identities are `live`, and whose protocols are given by `protocolOf`.

`LedgerDelta.WellFormed` checks *shape*: that a split goes somewhere and a join
comes from somewhere. That is not enough, and an earlier transition relation
proved it: with shape alone, `join [ghost₁, ghost₂] into` erased two identities
that were never live and installed a duty from nothing, `split ghost [a, b]`
installed two, and `discharge ghost` silently no-opped. All three are what
`docs/OBLIGATIONS.md` §2 names — "Dropping, duplicating, or fabricating
obligations is forbidden" — and `docs/FOUNDATION.md` law 7 states as no obligation
disappearance.

The protocol conditions are §2's other half: the ledger changes "only through the
owning protocol theorem", so a split may not produce duties governed by a
different protocol than the one it divides, and a join may not merge duties from
several.
-/
def Applicable (live : List ObligationId)
    (protocolOf : ObligationId → Option ObligationProtocolId) : LedgerDelta → Prop
  | .create o => o.id ∉ live
  | .discharge id => id ∈ live
  | .split source into =>
      source ∈ live ∧
      (∀ o ∈ into, o.id ∉ live ∨ o.id = source) ∧
      (∀ o ∈ into, protocolOf source = some o.protocol)
  | .join sources into =>
      (∀ id ∈ sources, id ∈ live) ∧
      (into.id ∉ live ∨ into.id ∈ sources) ∧
      (∀ id ∈ sources, protocolOf id = some into.protocol)
  | .transfer id _ => id ∈ live

instance (live : List ObligationId)
    (protocolOf : ObligationId → Option ObligationProtocolId) :
    (delta : LedgerDelta) → Decidable (Applicable live protocolOf delta)
  | .create _ => inferInstanceAs (Decidable (_ ∉ _))
  | .discharge _ => inferInstanceAs (Decidable (_ ∈ _))
  | .split _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .join _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .transfer _ _ => inferInstanceAs (Decidable (_ ∈ _))

/-- A discharge of an identity that is not live is not applicable. This is the
silent drop the transition used to perform. -/
theorem not_applicable_discharge_of_not_live {live : List ObligationId}
    {protocolOf : ObligationId → Option ObligationProtocolId} {id : ObligationId}
    (h : id ∉ live) : ¬ Applicable live protocolOf (.discharge id) := h

/-- A join whose sources were never live is not applicable. This is the
fabrication. -/
theorem not_applicable_join_of_dead_source {live : List ObligationId}
    {protocolOf : ObligationId → Option ObligationProtocolId}
    {sources : List ObligationId} {into : Obligation} {id : ObligationId}
    (hmem : id ∈ sources) (h : id ∉ live) :
    ¬ Applicable live protocolOf (.join sources into) := fun ha => h (ha.1 id hmem)

/-- A create of an identity that is already live is not applicable. This is the
duplication that silently overwrote a live duty. -/
theorem not_applicable_create_of_live {live : List ObligationId}
    {protocolOf : ObligationId → Option ObligationProtocolId} {o : Obligation}
    (h : o.id ∈ live) : ¬ Applicable live protocolOf (.create o) := fun ha => ha h

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

/-- The obligation kinds this effect creates, including through split and join.

A profile checks these, so a protocol cannot introduce a duty of a kind the
target never declared. -/
def createdKinds (effect : LedgerEffect) : List ObligationKindId :=
  effect.flatMap fun delta =>
    match delta with
    | .create o => [o.kind]
    | .split _ into => into.map Obligation.kind
    | .join _ into => [into.kind]
    | .discharge _ | .transfer _ _ => []

/-- Every identity this effect reassigns to a new owner. -/
def reowns (effect : LedgerEffect) : List ObligationId :=
  effect.flatMap LedgerDelta.reowns

/-- `effect.PreservesIdentity id` holds when no delta of `effect` touches `id`. -/
def PreservesIdentity (effect : LedgerEffect) (id : ObligationId) : Prop :=
  ∀ delta ∈ effect, delta.PreservesIdentity id

/-- `effect.WellFormed` holds when every delta is well formed. -/
def WellFormed (effect : LedgerEffect) : Prop :=
  ∀ delta ∈ effect, delta.WellFormed

@[simp] theorem wellFormed_nil : WellFormed [] := by simp [WellFormed]

@[simp] theorem reowns_nil : reowns [] = [] := rfl

@[simp] theorem createdKinds_nil : createdKinds [] = [] := rfl

instance (effect : LedgerEffect) : Decidable effect.WellFormed :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The empty effect changes nothing, which is the framing base case. -/
@[simp] theorem preservesIdentity_nil (id : ObligationId) :
    PreservesIdentity [] id := by simp [PreservesIdentity]

@[simp] theorem consumes_nil : consumes [] = [] := rfl

@[simp] theorem produces_nil : produces [] = [] := rfl

end LedgerEffect

end Grass.Obligation
