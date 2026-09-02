import Grass.Core.Context
import Grass.Core.Uid
import Grass.Core.Name

/-!
# Obligations

`docs/OBLIGATIONS.md` §1: an obligation is a linear ghost resource stating that
its holder must perform a future action or transfer responsibility under a named
protocol.

Two demands from §1 shape this module. Identity is unique and generative, because
an obligation is linear and two obligations of the same kind held by the same
context are still two obligations. Payloads are existential, "so new instruction,
API, ABI, allocator, lock, transaction, interrupt, and device protocols can extend
the ledger" without this module learning about them.

The consequence of an existential payload is that `Obligation` has no
`DecidableEq`. That is correct rather than inconvenient: the ledger is keyed by
`ObligationId`, which is decidable, and a proof that two obligations are the same
obligation must go through identity, never through comparing payloads.

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
An obligation's payload.

Existential: the payload's type is chosen by the protocol that created the
obligation, and this module cannot inspect it. That is what lets a device or
transaction protocol carry its own evidence in the same ledger as a lock.
-/
structure ObligationPayload : Type 1 where
  /-- The payload type, chosen by the creating protocol. -/
  Data : Type
  /-- The payload itself. -/
  data : Data

/--
An obligation: a linear ghost resource with an owner and a governing protocol.

The precondition, accepted discharge events, transfer rules, and cancellation
behavior that `docs/OBLIGATIONS.md` §1 also demands are properties of the named
protocol rather than fields here, and are stated by the M5 protocol theorems.
Carrying them as data would make every instruction model that creates an
obligation restate its protocol's rules.
-/
structure Obligation : Type 1 where
  /-- This obligation's generative identity. -/
  id : ObligationId
  /-- What kind of duty it is. -/
  kind : ObligationKindId
  /-- The protocol whose theorems may discharge, transfer, or split it. -/
  protocol : ObligationProtocolId
  /-- The context currently responsible for it. -/
  owner : ContextId
  /-- Protocol-owned evidence. -/
  payload : ObligationPayload

namespace Obligation

/-- Two obligations are the same obligation exactly when their identities agree.
Payloads are existential and are never compared. -/
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
