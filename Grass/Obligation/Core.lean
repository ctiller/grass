import Grass.Core.Context
import Grass.Core.Uid
import Grass.Core.Name

/-!
# Obligations

`docs/OBLIGATIONS.md` §1: an obligation is a linear ghost resource stating that
its holder must perform a future action or transfer responsibility under a named
protocol.

Identity is unique and generative, because an obligation is linear: two
obligations of the same kind held by the same context are still two obligations.

§1 also says payloads are existential, "so new instruction, API, ABI, allocator,
lock, transaction, interrupt, and device protocols can extend the ledger" without
this module learning about them. That openness is real and is preserved, but the
existential does **not** live here. An `Obligation` carries identity, kind,
protocol, and owner; protocol-specific evidence is held by the protocol, keyed by
`ObligationId`, and the operation that creates an obligation carries its own
evidence in the existential package that already exists for operations
(`Grass/Op/Facets.lean`).

Putting the existential in the obligation itself cost more than it bought. A
`Type 1` field propagated through `LedgerEffect` into `AccessDescriptor`, then
into `SubstepSequence` and every facet, and took `DecidableEq`, `Repr`, and
decidable well-formedness with it — so the sealed access descriptor became the
one thing in the layer an author could neither check by computation nor print in
a diagnostic. Keying evidence by identity gives the same extensibility at none of
that cost.

Scope note. This module is the M1 vocabulary of
`docs/MEMORY_IMPLEMENTATION_PLAN.md`. The ledger law, the block-contract
obligation sets, and the terminal disposition theorem are M5. What is here is the
shape an instruction or API model writes down, plus the nominal protocol
reference those later theorems are indexed by.
-/

namespace Grass.Obligation

open Grass.Core

/-- Phantom tag for obligation identities. -/
inductive ObligationTag : Type

/--
The generative identity of one obligation.

Linearity is about this identity: discharging an obligation consumes exactly this
one, and a second obligation of the same kind is untouched.
-/
abbrev ObligationId := Core.Uid ObligationTag

/--
The identity of an obligation kind.

Open nominal. The kinds named here are the examples `docs/OBLIGATIONS.md` §1
gives; a new protocol adds its own.
-/
structure ObligationKindId where
  /-- The kind's nominal name. -/
  name : Name
deriving DecidableEq, Repr

namespace ObligationKindId

/-- A lock was acquired and must be released. -/
def unlockAfterLock : ObligationKindId := ⟨⟨"unlockAfterLock"⟩⟩

/-- Interrupt state was masked and must be restored. -/
def restoreInterruptState : ObligationKindId := ⟨⟨"restoreInterruptState"⟩⟩

/-- An allocation was acquired and must be released. -/
def releaseAllocation : ObligationKindId := ⟨⟨"releaseAllocation"⟩⟩

/-- A transaction was begun and must be finished or aborted. -/
def finishTransaction : ObligationKindId := ⟨⟨"finishTransaction"⟩⟩

/-- A thread was spawned and must be joined or detached. -/
def joinOrDetachThread : ObligationKindId := ⟨⟨"joinOrDetachThread"⟩⟩

/-- ABI state was disturbed and must be restored. -/
def restoreAbiState : ObligationKindId := ⟨⟨"restoreAbiState"⟩⟩

/-- A partially completed I/O operation must be finished. -/
def completePartialIo : ObligationKindId := ⟨⟨"completePartialIo"⟩⟩

/-- Borrowed authority must be returned to its lender. -/
def returnBorrowedAuthority : ObligationKindId := ⟨⟨"returnBorrowedAuthority"⟩⟩

/-- A handle or descriptor was opened and must be closed. -/
def closeHandle : ObligationKindId := ⟨⟨"closeHandle"⟩⟩

end ObligationKindId

/--
The identity of the protocol that governs an obligation.

`docs/OBLIGATIONS.md` §2 permits the ledger to change "only through the owning
protocol theorem", so every obligation names the protocol whose theorem may act
on it. The reference is nominal here; the theorem it names is M5's.
-/
structure ObligationProtocolId where
  /-- The protocol's nominal name. -/
  name : Name
deriving DecidableEq, Repr

/--
Evidence that its holder may act under `protocol`.

`docs/OBLIGATIONS.md` §2 permits the ledger to change "only through the owning
protocol theorem". A ledger delta that merely *named* a protocol satisfied nothing —
comparing `ObligationProtocolId` values is comparing strings, and any caller could
write down any name. Indexing by the protocol stops one authority being *carried* to
another protocol: the type of an authority for one differs from the type for another,
and the elaborator rejects the substitution.

**Indexing alone stops nothing, and an earlier version of this docstring implied it
did.** The structure had a public constructor, so `⟨⟨"attacker.profile"⟩⟩` inhabited
it at every index — the criticism levelled at the nominal design applied verbatim to
its replacement, and the elaborator only stopped a caller *reusing* an existing value,
which no caller needs to do. Review demonstrated it in three lines. `mk` is private
now and `mintedBy` below is the one door, which is not a capability but is auditable:
there is a single place to look, and it records who minted.

That is the type-level half. The state-level half is in `LedgerDelta.Applicable`,
which checks that the protocol a delta claims authority under is the protocol the
live obligation actually has. Neither half suffices alone: typing stops authority
being carried across protocols, and applicability stops it being claimed over an
obligation it does not govern.

What this still does **not** establish is that the holder legitimately obtained the
authority. `mintedBy` is callable by anyone who can name a profile, and no rule says
which profile may mint for which protocol; `issuer` records the claim so a §10
package has something to check. This is an open obligation for M10's profile closure,
and it is a smaller one than it was, because there is now exactly one place authority
enters.
-/
structure ProtocolAuthority (protocol : ObligationProtocolId) where
  private mk ::
  /-- The profile that minted this authority. -/
  issuer : Name
deriving DecidableEq, Repr

namespace ProtocolAuthority

/-- Mint authority for `protocol`, recording which profile did so.

The one door. **Not a capability check, and until review it was not a check of any
kind**: this function is public, total and unconditioned, so any module can mint
authority for any protocol, and review did — a value built from a string in a file
that owns nothing, used to discharge a duty another family had created under its own
protocol, with no violation recorded. The type index stops authority for one protocol
being *presented* for another and says nothing about where the value came from.

Two things check it now, neither of them a capability.
`AdmittedVocabulary.protocols` is the registry a profile declares, and
`AdmittedVocabulary.admissibilityFailures` refuses a descriptor whose ledger effect
claims a protocol the profile never declared — which is what `GrantKind` already had
and this did not. `Tools/DoorAudit.py` keeps a `Grass/` caller from minting outside
this module.

`issuer` is still read by nothing but this file's own simp lemma. It is a record for
a report that does not exist yet; §10's profile closure is where it would be
consumed. -/
def mintedBy (protocol : ObligationProtocolId) (issuer : Name) :
    ProtocolAuthority protocol := ⟨issuer⟩

@[simp] theorem issuer_mintedBy (protocol : ObligationProtocolId) (issuer : Name) :
    (mintedBy protocol issuer).issuer = issuer := rfl

end ProtocolAuthority

/--
An obligation: a linear ghost resource with an owner and a governing protocol.

The precondition, accepted discharge events, transfer rules, and cancellation
behavior that `docs/OBLIGATIONS.md` §1 also demands are properties of the named
protocol rather than fields here, and are stated by the M5 protocol theorems.
Carrying them as data would make every instruction model that creates an
obligation restate its protocol's rules.
-/
structure Obligation where
  /-- This obligation's generative identity. -/
  id : ObligationId
  /-- What kind of duty it is. -/
  kind : ObligationKindId
  /-- The protocol whose theorems may discharge, transfer, or split it. -/
  protocol : ObligationProtocolId
  /-- The context currently responsible for it. -/
  owner : ContextId
deriving DecidableEq, Repr

namespace Obligation

/-- Two obligations are the same obligation exactly when their identities agree.
Kind, protocol, and owner are properties of an obligation, not what makes it that
obligation: a transfer changes the owner and the duty is unchanged. -/
def Same (a b : Obligation) : Prop := a.id = b.id

instance (a b : Obligation) : Decidable (a.Same b) :=
  inferInstanceAs (Decidable (a.id = b.id))

theorem Same.refl (a : Obligation) : a.Same a := rfl

theorem Same.symm {a b : Obligation} (h : a.Same b) : b.Same a := Eq.symm h

theorem Same.trans {a b c : Obligation} (h₁ : a.Same b) (h₂ : b.Same c) : a.Same c :=
  Eq.trans h₁ h₂

/-- Reassign an obligation to another context. The identity, kind, protocol, and
payload are preserved, so a transfer moves responsibility without creating a new
duty or losing the old one. -/
def transferTo (o : Obligation) (owner : ContextId) : Obligation := { o with owner }

@[simp] theorem transferTo_id (o : Obligation) (owner : ContextId) :
    (o.transferTo owner).id = o.id := rfl

@[simp] theorem transferTo_kind (o : Obligation) (owner : ContextId) :
    (o.transferTo owner).kind = o.kind := rfl

@[simp] theorem transferTo_protocol (o : Obligation) (owner : ContextId) :
    (o.transferTo owner).protocol = o.protocol := rfl

@[simp] theorem transferTo_owner (o : Obligation) (owner : ContextId) :
    (o.transferTo owner).owner = owner := rfl

theorem same_transferTo (o : Obligation) (owner : ContextId) : o.Same (o.transferTo owner) :=
  rfl

end Obligation

end Grass.Obligation
