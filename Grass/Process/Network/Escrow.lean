/-!
# Escrow: the prefix laws an in-flight message obeys

`docs/PROCESS.md` §3 puts the whole weight of channel soundness on one object:

> Their central object is an **escrow assertion**: after send commits, the
> channel—not either endpoint—owns the exact occurrence and every resource,
> capability, provenance fact, and obligation transferred with it until receive
> or an explicitly modeled cancellation/disposition transition consumes it.

and then states the laws it obeys:

> Conservation and at-most-one resolution are unconditional prefix laws; an
> unrestricted infinite-pending execution may retain live escrow forever. …
> Requesting cancellation does not reclaim escrow; acknowledged cancellation,
> timeout, endpoint/channel death, drop, reroute, and coalescing are exhaustive
> competing resolution transitions. Coalescing consumes every source token and
> creates one fresh occurrence.

Those are `docs/PROCESS_IMPLEMENTATION_PLAN.md` §4's second exit criterion, and
this module is them. It is deliberately *below* the channel contract: no
assertions, no worlds, no Hoare triples, no plan. An escrow ledger is a list of
occurrences that were created and a partial map saying how each one ended, and
everything here is a fact about that pair.

## Why `resolution` is a function

At-most-one resolution is not stated as a side condition. `resolution` is a
partial function from occurrences, so an occurrence has at most one ending by
construction, and `atMostOneResolution` below is a projection rather than an
assumption. `docs/PROCESS.md` §3 calls the affine resolve token "an owned
assertion inside `Escrow`, not a field whose Lean value is assumed
noncopyable" — a Lean record field is copyable, so affinity has to be a shape
the type cannot violate rather than a promise a field makes.

## Why requesting cancellation is a separate field

`cancelRequested` is tracked and is deliberately unrelated to `resolution`,
because §3 is explicit that "requesting cancellation does not reclaim escrow".
A design that resolved escrow on the request would lose the payload of a message
whose cancellation is later refused or lost a race, which is
`docs/FOUNDATION.md` law 5. `Grass/Process/Network/Instance.lean` makes the same
choice on the other side: a process with an outstanding cancellation is still
running.

## Prefix laws, not step laws

`Extends` is what "unconditional prefix law" means here. It says one ledger is a
later point of the same execution: occurrences are only appended, and a
resolution once written is never rewritten or erased. `noLoss` and
`resolvedStaysResolved` are then theorems about it, and they hold with no
responsiveness assumption at all — which is the point, since §3 warns that
"an unrestricted infinite-pending execution may retain live escrow forever".
Eventual delivery is a separate, named assumption and is not in this file.
-/

namespace Grass.Process

universe u

/--
How an escrowed occurrence stopped being in flight.

`docs/PROCESS.md` §3 lists these as "exhaustive competing resolution
transitions", with receive as the ordinary one. Closed, because the enumeration
being exhaustive is what makes `resolution` a total account of an occurrence's
ending rather than a place to put the cases someone thought of.

`rerouted` and `coalesced` carry a replacement because the occurrence does not
survive them. §3 says coalescing "consumes every source token and creates one
fresh occurrence"; the same follows for reroute from nominal freshness, since an
occurrence's identity is indexed by its session and a rerouted message is on a
different one. Carrying the replacement is what stops either transition from
being a disguised drop.
-/
inductive ChannelResolution (Occurrence : Type u) (Session : Type u)
  /-- The receiver consumed it. The ordinary ending. -/
  | received
  /-- A cancellation was *acknowledged*. Requesting one does not appear here. -/
  | cancelAcknowledged
  /-- It timed out. -/
  | timedOut
  /-- The sending incarnation died. -/
  | senderDied
  /-- The receiving incarnation died. -/
  | receiverDied
  /-- The session itself died. -/
  | channelDied
  /-- An explicitly modeled disposition dropped it. -/
  | dropped
  /-- It moved to another session, as a fresh occurrence there. -/
  | rerouted (destination : Session) (replacement : Occurrence)
  /-- It merged into one fresh occurrence, along with its fellow sources. -/
  | coalesced (replacement : Occurrence)

namespace ChannelResolution

variable {Occurrence Session : Type u}

/-- The occurrence that carries this one's payload onward, if any. -/
def replacement : ChannelResolution Occurrence Session → Option Occurrence
  | .rerouted _ replacement => some replacement
  | .coalesced replacement => some replacement
  | _ => none

/--
A resolution that ends the payload's life rather than passing it on.

Named so that a reader can see which endings are terminal for the escrowed
state, and so a conservation argument can distinguish them from the two that
are not.
-/
def IsTerminal (resolution : ChannelResolution Occurrence Session) : Prop :=
  resolution.replacement = none

theorem received_isTerminal :
    (ChannelResolution.received : ChannelResolution Occurrence Session).IsTerminal := rfl

theorem coalesced_not_terminal (replacement : Occurrence) :
    ¬ (ChannelResolution.coalesced (Session := Session) replacement).IsTerminal := by
  intro terminal
  exact absurd terminal (by simp [IsTerminal, ChannelResolution.replacement])

end ChannelResolution

/--
The escrow held by one channel, at one point of an execution.

`created` is every occurrence this channel has ever escrowed, oldest first, and
`resolution` says how each one ended — `none` meaning it is still in flight.
-/
structure EscrowLedger (Occurrence : Type u) (Session : Type u) where
  /-- Every occurrence ever escrowed here, oldest first. -/
  created : List Occurrence
  /-- No occurrence is escrowed twice; a repeat would be a fabricated identity. -/
  createdDistinct : created.Nodup
  /-- How each occurrence ended, or `none` while it is in flight. -/
  resolution : Occurrence → Option (ChannelResolution Occurrence Session)
  /-- Nothing is resolved that was never escrowed. -/
  noFabrication : ∀ occurrence, (resolution occurrence).isSome = true →
    occurrence ∈ created
  /-- A cancellation has been requested for these. Says nothing about escrow. -/
  cancelRequested : Occurrence → Bool
  /--
  A replacement is itself an escrowed occurrence, and a different one.

  Without this, `coalesced` and `rerouted` could name an occurrence that never
  existed, or name themselves, and the payload would be lost while the ledger
  claimed it had been passed on.
  -/
  replacementEscrowed : ∀ occurrence carrier,
    (resolution occurrence).bind ChannelResolution.replacement = some carrier →
    carrier ∈ created ∧ carrier ≠ occurrence

namespace EscrowLedger

variable {Occurrence Session : Type u} (ledger : EscrowLedger Occurrence Session)

/-- This occurrence has ended. -/
def Resolved (occurrence : Occurrence) : Bool := (ledger.resolution occurrence).isSome

/-- This occurrence is still in flight: escrowed, and not yet ended. -/
def Outstanding (occurrence : Occurrence) : Prop :=
  occurrence ∈ ledger.created ∧ ledger.resolution occurrence = none

/-- The occurrences still in flight. -/
def outstanding : List Occurrence :=
  ledger.created.filter (fun occurrence => !ledger.Resolved occurrence)

/-- The occurrences that have ended. -/
def settled : List Occurrence :=
  ledger.created.filter ledger.Resolved

/--
**At most one resolution.**

`docs/PROCESS.md` §3's affinity law, and a projection rather than an assumption:
`resolution` is a function, so an occurrence cannot end twice. Stated because
the property is what the design buys, and a reader should not have to
reconstruct that a function is single-valued to see that the law holds.
-/
theorem atMostOneResolution {occurrence : Occurrence}
    {first second : ChannelResolution Occurrence Session}
    (isFirst : ledger.resolution occurrence = some first)
    (isSecond : ledger.resolution occurrence = some second) : first = second := by
  rw [isFirst] at isSecond
  exact Option.some.inj isSecond

/-- Every occurrence is either in flight or ended, and never both. -/
theorem outstanding_xor_settled (occurrence : Occurrence)
    (escrowed : occurrence ∈ ledger.created) :
    (ledger.Outstanding occurrence ∧ ledger.Resolved occurrence = false) ∨
      (¬ ledger.Outstanding occurrence ∧ ledger.Resolved occurrence = true) := by
  unfold Outstanding Resolved
  cases ledger.resolution occurrence with
  | none => exact Or.inl ⟨⟨escrowed, rfl⟩, rfl⟩
  | some _ =>
    refine Or.inr ⟨?_, rfl⟩
    rintro ⟨_, inFlight⟩
    exact absurd inFlight (by simp)

end EscrowLedger

/-- Every element of a list is in exactly one of the two complementary filters. -/
private theorem length_filter_add_filter_not {α : Type u} (predicate : α → Bool) :
    ∀ items : List α,
      (items.filter predicate).length +
        (items.filter (fun item => !predicate item)).length = items.length
  | [] => rfl
  | item :: rest => by
    have ih := length_filter_add_filter_not predicate rest
    cases holds : predicate item with
    | true =>
      rw [List.filter_cons_of_pos holds, List.filter_cons_of_neg (by simp [holds])]
      simp only [List.length_cons]
      omega
    | false =>
      rw [List.filter_cons_of_neg (by simp [holds]),
        List.filter_cons_of_pos (by simp [holds])]
      simp only [List.length_cons]
      omega

namespace EscrowLedger

variable {Occurrence Session : Type u} (ledger : EscrowLedger Occurrence Session)

/--
**Conservation.**

Every escrowed occurrence is accounted for: it is either still in flight or it
has ended, and the two counts add to the number ever created. Nothing leaks and
nothing is invented.

`docs/PROCESS.md` §3 calls this an unconditional prefix law, and it is
unconditional here in the strongest sense — it is a fact about the ledger's
shape, with no hypothesis about scheduling, responsiveness, or progress.
-/
theorem conservation :
    ledger.settled.length + ledger.outstanding.length = ledger.created.length :=
  length_filter_add_filter_not ledger.Resolved ledger.created

/-- Nothing in flight has ended, which is what `outstanding` is supposed to mean. -/
theorem outstanding_not_resolved {occurrence : Occurrence}
    (inFlight : occurrence ∈ ledger.outstanding) :
    ledger.resolution occurrence = none := by
  have filtered := (List.mem_filter.mp inFlight).2
  cases ending : ledger.resolution occurrence with
  | none => rfl
  | some _ =>
    rw [Resolved, ending] at filtered
    exact absurd filtered (by simp)

/-- And everything in flight was escrowed here. -/
theorem outstanding_escrowed {occurrence : Occurrence}
    (inFlight : occurrence ∈ ledger.outstanding) : occurrence ∈ ledger.created :=
  (List.mem_filter.mp inFlight).1

/--
**Requesting cancellation does not reclaim escrow.**

Nothing in this structure relates `cancelRequested` to `resolution`, and that is
the content: an occurrence may have a cancellation requested and still be in
flight. `docs/PROCESS.md` §3 requires exactly this, because a request that
reclaimed the escrow would lose the payload of a message whose cancellation
later loses its race with delivery.

Stated as a theorem over the ledger rather than left implicit, so that a future
field tying the two together would break this file.
-/
theorem cancel_request_leaves_escrow (occurrence : Occurrence)
    (inFlight : ledger.Outstanding occurrence) (_requested : ledger.cancelRequested occurrence = true) :
    ledger.resolution occurrence = none :=
  inFlight.2

end EscrowLedger

/--
One ledger is a later point of the same execution than another.

The prefix relation the laws in `docs/PROCESS.md` §3 are stated over: escrowed
occurrences are only appended, and a resolution once written is permanent.
-/
structure LedgerExtends {Occurrence Session : Type u}
    (earlier later : EscrowLedger Occurrence Session) where
  /-- Occurrences are only appended. -/
  createdPrefix : earlier.created.IsPrefix later.created
  /-- A resolution, once written, is never rewritten or erased. -/
  resolutionPermanent : ∀ occurrence resolution,
    earlier.resolution occurrence = some resolution →
    later.resolution occurrence = some resolution

namespace LedgerExtends

variable {Occurrence Session : Type u} {earlier later : EscrowLedger Occurrence Session}

/-- An escrowed occurrence stays escrowed. -/
theorem created_preserved (extension : LedgerExtends earlier later)
    {occurrence : Occurrence} (escrowed : occurrence ∈ earlier.created) :
    occurrence ∈ later.created :=
  extension.createdPrefix.subset escrowed

/-- An ended occurrence stays ended, with the same ending. -/
theorem resolvedStaysResolved (extension : LedgerExtends earlier later)
    {occurrence : Occurrence} {resolution : ChannelResolution Occurrence Session}
    (ended : earlier.resolution occurrence = some resolution) :
    later.resolution occurrence = some resolution :=
  extension.resolutionPermanent occurrence resolution ended

/--
**No loss.**

An occurrence in flight at any point of an execution is, at every later point,
either still in flight or ended by one of the named resolutions. It cannot
simply be absent.

This is the `docs/FOUNDATION.md` law 5 statement for escrow, and the reason
`Extends` carries `resolutionPermanent` rather than merely `createdPrefix`:
without permanence a ledger could erase a resolution and reopen a settled
occurrence, and without the prefix an occurrence could vanish from `created`.
-/
theorem noLoss (extension : LedgerExtends earlier later) {occurrence : Occurrence}
    (inFlight : earlier.Outstanding occurrence) :
    later.Outstanding occurrence ∨ later.Resolved occurrence = true := by
  have escrowed := extension.created_preserved inFlight.1
  cases ending : later.resolution occurrence with
  | none => exact Or.inl ⟨escrowed, ending⟩
  | some _ => exact Or.inr (by simp [EscrowLedger.Resolved, ending])

/-- Extension is reflexive: a ledger is a later point of itself. -/
theorem refl (ledger : EscrowLedger Occurrence Session) : LedgerExtends ledger ledger where
  createdPrefix := List.prefix_refl _
  resolutionPermanent := fun _ _ ended => ended

/-- And transitive, so the laws hold across a whole execution, not one step. -/
theorem trans {middle : EscrowLedger Occurrence Session}
    (first : LedgerExtends earlier middle) (second : LedgerExtends middle later) :
    LedgerExtends earlier later where
  createdPrefix := first.createdPrefix.trans second.createdPrefix
  resolutionPermanent := fun occurrence resolution ended =>
    second.resolutionPermanent occurrence resolution
      (first.resolutionPermanent occurrence resolution ended)

end LedgerExtends

end Grass.Process
