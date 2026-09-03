import Grass.Process.Network.Mailbox

/-!
# A mailbox with something in it

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.85. An emptiness sweep over every
structure in the corpus found `Grass/Process/Network/Mailbox.lean` entirely
unwitnessed: `MailboxEntry` was constructed nowhere, `Mailbox`'s only inhabitant
anywhere was `Mailbox.empty`, and `SelectiveReceive` — nine fields, five of them
Props — had never been built at all.

What that costs is specific, not general. `Mailbox.distinct` had never been
discharged at a non-empty list, so the duplicate-freedom law was checked by
nothing; `PerSenderPair` had never been evaluated at a mailbox with an entry; and
every one of `SelectiveReceive`'s five laws was a claim about a relation with no
inhabitants.

This file is the smallest thing that fixes that, and it is deliberately not the
smallest thing that *inhabits* it. A one-entry mailbox whose only entry matches
would discharge `skippedRejected` and `exhaustedIfNone` vacuously and leave
`scanWork` at zero. `theReceive` below scans *past* a non-matching entry to
select the second, so `skipped` is non-empty, `skippedRejected` has something to
reject, and `scanWorkExact` reports a scan that actually cost something.
-/

namespace Grass.Process.Tests.Mailbox

open Grass.Process

/-- The three parameters, at the simplest types that can tell entries apart. -/
abbrev Carrier := Nat
/-- Senders are numbered. -/
abbrev Sender := Nat
/-- And so are payloads, which is what the filter reads. -/
abbrev Payload := Nat

/-- One entry: an occurrence identity, a sender, a payload. -/
def entryOf (carrier : Carrier) (sender : Sender) (payload : Payload) :
    MailboxEntry Carrier Sender Payload where
  occurrence := ⟨.messageOccurrence, carrier⟩
  isMessage := rfl
  sender := sender
  payload := payload

/--
**A mailbox holding two entries.**

The first non-empty `Mailbox` in the corpus, and therefore the first discharge of
`distinct` that is not vacuous: the two entries carry different occurrence
identities, and `decide` has to check it.
-/
def twoEntry : Mailbox Carrier Sender Payload where
  entries := [entryOf 0 0 7, entryOf 1 0 9]
  distinct := by decide

/-- A filter that accepts only payload 9, so the first entry is scanned past. -/
def acceptsNine (entry : MailboxEntry Carrier Sender Payload) : Bool := entry.payload == 9

/--
**A selective receive that skips one entry and selects the next.**

Every field is discharged against a scan that actually happened: `skipped` holds
the rejected entry, `selected` holds the accepted one, `rest` is what remained,
and `scanWork` is one rather than zero.
-/
def theReceive : SelectiveReceive twoEntry acceptsNine where
  skipped := [entryOf 0 0 7]
  selected := some (entryOf 1 0 9)
  rest := []
  exact := rfl
  skippedRejected := by decide
  selectedAccepted := by decide
  exhaustedIfNone := by simp
  scanWork := 1
  scanWorkExact := rfl

/-- And the scan cost what the scan cost: one skipped entry, one unit of work. -/
theorem the_receive_scanned_one : theReceive.scanWork = 1 := rfl

/-- The entry it skipped is one the filter really rejects. -/
theorem the_skipped_entry_is_rejected : acceptsNine (entryOf 0 0 7) = false := rfl

/-- And the one it took is one the filter really accepts. -/
theorem the_selected_entry_is_accepted : acceptsNine (entryOf 1 0 9) = true := rfl

end Grass.Process.Tests.Mailbox
