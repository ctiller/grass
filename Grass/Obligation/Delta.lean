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

**And a transfer's destination went unchecked.** The clause read
`id ∈ live ∧ protocolOf id = some claimed ∧ ownerOf id = some actor` and said nothing
about `newOwner`, so a duty could be handed to an identity no context ever had.
Discharge requires the actor to own the obligation, so nothing could ever discharge
it: `docs/OBLIGATIONS.md` §3's terminal disposition is false of that ledger under
every execution, which makes it a way to strand a duty permanently rather than a way
to drop one. The destination must be a context the machine knows, which is why
`Applicable` takes the context set — `MachineState.contexts` under
`Grass/Op/Step.lean`, the same set `ContextKind` agreement is checked against.

**The second of those was false of deltas `Applicable` accepted**, and review found
it. `split`'s clause was `∀ o ∈ into, o.id ∉ live ∨ o.id = source` and `join`'s was
`into.id ∉ live ∨ into.id ∈ sources`, so an output could reuse an input's identity.
Outputs must be fresh now: §3 does not ask for identity reuse, identities come from a
supply that never reissues, and the law above is a law again.

**And the `kind` was unpinned, which is the defect that mattered and which the
freshness rule did not close.** `Applicable` pinned each output's protocol and owner
and not its kind, so a one-element split — now with a *fresh* identity — still
replaced a live duty of one kind with an unrelated duty of another, and no `discharge`
appeared anywhere in the effect. Review demonstrated it a second time after the
freshness repair, on the same clause the first repair's own commit message had
diagnosed. `docs/OBLIGATIONS.md`'s split is "one obligation becomes several, together
covering the same duty", and a duty of a different kind is not the same duty, so every
output's kind must be the source's — and a join's source kinds must be the output's.
`Applicable` takes a `kindOf` for it.
-/

namespace Grass.Obligation

open Grass.Core

/--
One change a transition makes to the obligation ledger.

An obligation not named by any delta of a transition is preserved unchanged.
-/
inductive LedgerDelta where
  /-- A protocol created a new obligation. -/
  | create (claimed : ObligationProtocolId) (authority : ProtocolAuthority claimed)
      (obligation : Obligation)
  /-- The required action occurred and this obligation ends. -/
  | discharge (claimed : ObligationProtocolId) (authority : ProtocolAuthority claimed)
      (obligation : ObligationId)
  /-- One obligation becomes several, together covering the same duty. -/
  | split (claimed : ObligationProtocolId) (authority : ProtocolAuthority claimed)
      (source : ObligationId) (into : List Obligation)
  /-- Several obligations become one. -/
  | join (claimed : ObligationProtocolId) (authority : ProtocolAuthority claimed)
      (sources : List ObligationId) (into : Obligation)
  /-- Responsibility moves to another context; the duty itself is unchanged. -/
  | transfer (claimed : ObligationProtocolId) (authority : ProtocolAuthority claimed)
      (obligation : ObligationId) (newOwner : ContextId)
deriving DecidableEq, Repr

namespace LedgerDelta

/--
The identities this delta removes from the ledger.

A transfer consumes nothing: `docs/OBLIGATIONS.md` §1 makes transfer a change of
owner, not an end of the duty, and the identity survives it.
-/
def consumes : LedgerDelta → List ObligationId
  | .create _ _ _ => []
  | .discharge _ _ id => [id]
  | .split _ _ source _ => [source]
  | .join _ _ sources _ => sources
  | .transfer _ _ _ _ => []

/-- The protocol this delta claims authority under. -/
def claimedProtocol : LedgerDelta → ObligationProtocolId
  | .create claimed _ _ | .discharge claimed _ _ | .split claimed _ _ _
  | .join claimed _ _ _ | .transfer claimed _ _ _ => claimed

/-- The identities this delta adds to the ledger. -/
def produces : LedgerDelta → List ObligationId
  | .create _ _ obligation => [obligation.id]
  | .discharge _ _ _ => []
  | .split _ _ _ into => into.map Obligation.id
  | .join _ _ _ into => [into.id]
  | .transfer _ _ _ _ => []

/--
The identities this delta leaves in place but reassigns to another owner.

Separate from `consumes` and `produces` because a transfer does neither: the duty
survives with its identity intact. It is nonetheless a change to that
obligation's row in the ledger, which is why `PreservesIdentity` has to see it.
-/
def reowns : LedgerDelta → List ObligationId
  | .transfer _ _ id _ => [id]
  | .create _ _ _ | .discharge _ _ _ | .split _ _ _ _ | .join _ _ _ _ => []

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
  | .create _ _ _ => True
  | .discharge _ _ _ => True
  | .split _ _ _ into => into ≠ [] ∧ (into.map Obligation.id).Nodup
  | .join _ _ sources _ => sources ≠ [] ∧ sources.Nodup
  | .transfer _ _ _ _ => True

instance : (delta : LedgerDelta) → Decidable delta.WellFormed
  | .create _ _ _ => .isTrue trivial
  | .discharge _ _ _ => .isTrue trivial
  | .split _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .join _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | .transfer _ _ _ _ => .isTrue trivial

@[simp] theorem wellFormed_create (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (obligation : Obligation) :
    (LedgerDelta.create claimed authority obligation).WellFormed := trivial

@[simp] theorem wellFormed_discharge (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (id : ObligationId) :
    (LedgerDelta.discharge claimed authority id).WellFormed := trivial

@[simp] theorem wellFormed_transfer (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (id : ObligationId) (owner : ContextId) :
    (LedgerDelta.transfer claimed authority id owner).WellFormed := trivial

/-- A split into nothing is not a split; it is a disappearance. -/
theorem not_wellFormed_split_nil (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (source : ObligationId) :
    ¬ (LedgerDelta.split claimed authority source []).WellFormed := fun h => h.1 rfl

/-- A join from nothing is not a join; it is a fabrication. -/
theorem not_wellFormed_join_nil (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (into : Obligation) :
    ¬ (LedgerDelta.join claimed authority [] into).WellFormed := fun h => h.1 rfl

@[simp] theorem consumes_transfer (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (id : ObligationId) (owner : ContextId) :
    (LedgerDelta.transfer claimed authority id owner).consumes = [] := rfl

@[simp] theorem produces_transfer (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (id : ObligationId) (owner : ContextId) :
    (LedgerDelta.transfer claimed authority id owner).produces = [] := rfl

@[simp] theorem consumes_create (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (obligation : Obligation) :
    (LedgerDelta.create claimed authority obligation).consumes = [] := rfl

@[simp] theorem produces_create (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (obligation : Obligation) :
    (LedgerDelta.create claimed authority obligation).produces = [obligation.id] := rfl

@[simp] theorem consumes_discharge (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (id : ObligationId) :
    (LedgerDelta.discharge claimed authority id).consumes = [id] := rfl

@[simp] theorem produces_discharge (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (id : ObligationId) :
    (LedgerDelta.discharge claimed authority id).produces = [] := rfl

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
    (claimed : ObligationProtocolId) (authority : ProtocolAuthority claimed)
    (owner : ContextId) :
    (LedgerDelta.transfer claimed authority moved owner).PreservesIdentity id :=
  ⟨by simp, by simp, by simp [reowns, h]⟩

/-- The moved obligation is not preserved: a transfer is a change to its row. -/
theorem not_preservesIdentity_transfer_self (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (moved : ObligationId) (owner : ContextId) :
    ¬ (LedgerDelta.transfer claimed authority moved owner).PreservesIdentity moved := by
  rintro ⟨_, _, hr⟩
  exact hr (by simp [reowns])

/-- A transfer neither consumes nor produces, so the duty's identity survives it.
This is what distinguishes transfer from discharge-and-recreate. -/
theorem identity_survives_transfer (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) (moved : ObligationId) (owner : ContextId) :
    (LedgerDelta.transfer claimed authority moved owner).consumes = [] ∧
      (LedgerDelta.transfer claimed authority moved owner).produces = [] := ⟨rfl, rfl⟩

/-- A discharge consumes exactly the obligation it names and no other. -/
theorem preservesIdentity_discharge_of_ne {discharged id : ObligationId}
    (h : id ≠ discharged) (claimed : ObligationProtocolId)
    (authority : ProtocolAuthority claimed) :
    (LedgerDelta.discharge claimed authority discharged).PreservesIdentity id :=
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
owning protocol theorem".

That half is now split between the type and this predicate. Every delta carries a
`ProtocolAuthority claimed` — indexed by the protocol, so authority for one cannot
be presented for another — and the clauses below check that `claimed` is the
protocol the live obligation actually has. An earlier version compared
`ObligationProtocolId` values only, which is comparing strings any caller could
write down, and carried no authority at all.
-/
def Applicable (live : List ObligationId)
    (protocolOf : ObligationId → Option ObligationProtocolId)
    (ownerOf : ObligationId → Option ContextId)
    (kindOf : ObligationId → Option ObligationKindId) (contexts : List ContextId)
    (actor : ContextId) : LedgerDelta → Prop
  | .create claimed _ o => o.id ∉ live ∧ o.protocol = claimed ∧ o.owner = actor
  | .discharge claimed _ id =>
      id ∈ live ∧ protocolOf id = some claimed ∧ ownerOf id = some actor
  | .split claimed _ source into =>
      source ∈ live ∧ protocolOf source = some claimed ∧
      ownerOf source = some actor ∧
      (∀ o ∈ into, o.id ∉ live) ∧
      (∀ o ∈ into, o.protocol = claimed) ∧
      (∀ o ∈ into, o.owner = actor) ∧
      (∀ o ∈ into, kindOf source = some o.kind)
  | .join claimed _ sources into =>
      (∀ id ∈ sources, id ∈ live) ∧
      (∀ id ∈ sources, protocolOf id = some claimed) ∧
      (∀ id ∈ sources, ownerOf id = some actor) ∧
      (∀ id ∈ sources, kindOf id = some into.kind) ∧
      into.id ∉ live ∧
      into.protocol = claimed ∧ into.owner = actor
  | .transfer claimed _ id newOwner =>
      id ∈ live ∧ protocolOf id = some claimed ∧ ownerOf id = some actor ∧
      newOwner ∈ contexts

instance (live : List ObligationId)
    (protocolOf : ObligationId → Option ObligationProtocolId)
    (ownerOf : ObligationId → Option ContextId)
    (kindOf : ObligationId → Option ObligationKindId) (contexts : List ContextId)
    (actor : ContextId) : (delta : LedgerDelta) →
      Decidable (Applicable live protocolOf ownerOf kindOf contexts actor delta)
  | .create _ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .discharge _ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .split _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
  | .join _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
  | .transfer _ _ _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A discharge of an identity that is not live is not applicable. This is the
silent drop the transition used to perform. -/
theorem not_applicable_discharge_of_not_live {live : List ObligationId}
    {protocolOf : ObligationId → Option ObligationProtocolId}
    {ownerOf : ObligationId → Option ContextId}
    {kindOf : ObligationId → Option ObligationKindId} {contexts : List ContextId}
    {actor : ContextId} {id : ObligationId}
    {claimed : ObligationProtocolId} {authority : ProtocolAuthority claimed}
    (h : id ∉ live) :
    ¬ Applicable live protocolOf ownerOf kindOf contexts actor (.discharge claimed authority id) :=
  fun ha => h ha.1

/-- Authority for one protocol does not authorize a duty governed by another.
This is the state-level half; the type-level half is that a
`ProtocolAuthority p` is not a `ProtocolAuthority q`. -/
theorem not_applicable_discharge_of_wrong_protocol {live : List ObligationId}
    {protocolOf : ObligationId → Option ObligationProtocolId}
    {ownerOf : ObligationId → Option ContextId}
    {kindOf : ObligationId → Option ObligationKindId} {contexts : List ContextId}
    {actor : ContextId} {id : ObligationId}
    {claimed : ObligationProtocolId} {authority : ProtocolAuthority claimed}
    (h : protocolOf id ≠ some claimed) :
    ¬ Applicable live protocolOf ownerOf kindOf contexts actor (.discharge claimed authority id) :=
  fun ha => h ha.2.1

/--
**A duty is discharged by its holder, not by whoever runs next.**

`docs/OBLIGATIONS.md` opens by making an obligation a duty of "its holder" and §1
lists the owner as part of its form. `Obligation.owner` was carried, printed, and
consulted by nothing: liveness and protocol were checked, ownership was not, so
one context could discharge a duty another held. Local adversarial review stepped
a device engine through a discharge of the program thread's release obligation and
the duty vanished with no violation. Same class as the two registries nothing
consulted.
-/
theorem not_applicable_discharge_of_wrong_owner {live : List ObligationId}
    {protocolOf : ObligationId → Option ObligationProtocolId}
    {ownerOf : ObligationId → Option ContextId}
    {kindOf : ObligationId → Option ObligationKindId} {contexts : List ContextId}
    {actor : ContextId} {id : ObligationId}
    {claimed : ObligationProtocolId} {authority : ProtocolAuthority claimed}
    (h : ownerOf id ≠ some actor) :
    ¬ Applicable live protocolOf ownerOf kindOf contexts actor (.discharge claimed authority id) :=
  fun ha => h ha.2.2

/-- A join whose sources were never live is not applicable. This is the
fabrication. -/
theorem not_applicable_join_of_dead_source {live : List ObligationId}
    {protocolOf : ObligationId → Option ObligationProtocolId}
    {ownerOf : ObligationId → Option ContextId}
    {kindOf : ObligationId → Option ObligationKindId} {contexts : List ContextId}
    {actor : ContextId}
    {sources : List ObligationId} {into : Obligation} {id : ObligationId}
    {claimed : ObligationProtocolId} {authority : ProtocolAuthority claimed}
    (hmem : id ∈ sources) (h : id ∉ live) :
    ¬ Applicable live protocolOf ownerOf kindOf contexts actor (.join claimed authority sources into) :=
  fun ha => h (ha.1 id hmem)

/-- A create of an identity that is already live is not applicable. This is the
duplication that silently overwrote a live duty. -/
theorem not_applicable_create_of_live {live : List ObligationId}
    {protocolOf : ObligationId → Option ObligationProtocolId}
    {ownerOf : ObligationId → Option ContextId}
    {kindOf : ObligationId → Option ObligationKindId} {contexts : List ContextId}
    {actor : ContextId} {o : Obligation}
    {claimed : ObligationProtocolId} {authority : ProtocolAuthority claimed}
    (h : o.id ∈ live) :
    ¬ Applicable live protocolOf ownerOf kindOf contexts actor (.create claimed authority o) :=
  fun ha => ha.1 h

/-- A context may not create a duty in another's name either, which is the
fabrication half of ownership. -/
theorem not_applicable_create_of_wrong_owner {live : List ObligationId}
    {protocolOf : ObligationId → Option ObligationProtocolId}
    {ownerOf : ObligationId → Option ContextId}
    {kindOf : ObligationId → Option ObligationKindId} {contexts : List ContextId}
    {actor : ContextId} {o : Obligation}
    {claimed : ObligationProtocolId} {authority : ProtocolAuthority claimed}
    (h : o.owner ≠ actor) :
    ¬ Applicable live protocolOf ownerOf kindOf contexts actor (.create claimed authority o) :=
  fun ha => h ha.2.2

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
    | .create _ _ o => [o.kind]
    | .split _ _ _ into => into.map Obligation.kind
    | .join _ _ _ into => [into.kind]
    | .discharge _ _ _ | .transfer _ _ _ _ => []

/--
The protocols this effect claims authority under.

`ProtocolAuthority` is indexed by the protocol, so authority for one cannot be
*presented* for another — but `mintedBy` is public, total and unconditioned, so
authority for any protocol can be *minted* by anyone. Review built one out of a
string in a foreign module and used it to discharge a duty the ISA family had created
under its own protocol: no violation, duty gone. The type index restricts nothing
about where the value came from.

A profile checks these, exactly as it checks `createdKinds`, so an operation cannot
act under a protocol the target never declared. That is not a capability either —
`docs/OBLIGATIONS.md` §2's "only through the owning protocol theorem" needs a theorem
this layer cannot state — but it moves the claim from unchecked to declared, which is
what every other open nominal name in this tree got.
-/
def claimedProtocols (effect : LedgerEffect) : List ObligationProtocolId :=
  effect.map fun delta =>
    match delta with
    | .create claimed _ _ | .discharge claimed _ _ | .split claimed _ _ _
    | .join claimed _ _ _ | .transfer claimed _ _ _ => claimed

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
