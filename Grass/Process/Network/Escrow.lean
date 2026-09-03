import Grass.Process.Cancellation.Identity
import Grass.Process.Network.Death

/-!
# Escrow: what one channel is holding, and what it may do with it

`docs/PROCESS.md` §3 puts the weight of channel soundness on one object:

> Their central object is an **escrow assertion**: after send commits, the
> channel—not either endpoint—owns the exact occurrence and every resource,
> capability, provenance fact, and obligation transferred with it until receive
> or an explicitly modeled cancellation/disposition transition consumes it.

and states the laws it obeys:

> Conservation and at-most-one resolution are unconditional prefix laws …
> Requesting cancellation does not reclaim escrow; acknowledged cancellation,
> timeout, endpoint/channel death, drop, reroute, and coalescing are exhaustive
> competing resolution transitions. Coalescing consumes every source token and
> creates one fresh occurrence.

## What this module is, and what it is not

It is the **ledger-level half** of `docs/PROCESS_IMPLEMENTATION_PLAN.md` §4's
second exit criterion. That criterion asks for conservation, at-most-one
resolution, *and stability under unrelated steps*, over the *full transition
family*. Stability is `Grass/Process/Network/Assertion.lean`'s frame rule
applied to an escrow assertion, and the quantification over the family needs
`Transition.lean`. Neither is here. An earlier revision of this note claimed the
module was the criterion; it is the part of it that can be stated about a ledger
with no transitions in sight.

Three further claims that revision made and this one does not:

* **At-most-one *recorded ending*, not the affine resolve token.** `resolution`
  is a function, so an occurrence has at most one recorded ending by
  construction. §3's `ResolveToken` is stronger: it is consumed exactly once by
  exactly one transition. Two transitions could each consume the same source and
  record the same ending here, consistently. That half needs the transition
  family; this module delivers the recording half only.
* **"Coalescing consumes every source token" is not stated here.** A ledger has
  no notion of a transition, so it cannot say "every source of *this* coalesce".
  What it does say is that a coalesced occurrence names a real, strictly later
  carrier, which is what stops the constructor being a disguised drop.
* **`accounting` is a counting identity, not §3's prefix conservation.** It says
  the occurrences ever escrowed are exactly those settled plus those in flight.
  The prefix half — that this holds monotonically along an execution — is
  `settled_monotone` and `created_monotone` over `LedgerExtends`, and those are
  what §3's "unconditional prefix laws" names.

## Why `rank` exists

`coalesceCarrierLater` requires a coalesce to name a carrier of *strictly
greater* rank. Irreflexivity alone is not enough: with only "the carrier is
escrowed and is not this occurrence", two occurrences may coalesce into each
other, a chain may close into a cycle, and every field still discharges while
both payloads land nowhere. A ledger like that satisfies `accounting` and
reports itself in order.

`rank` is the occurrence's position in the monotone allocation history — §3's
`usedNominals` ordering — and `rankOrdersCreated` ties it to `created`, so there
is one order and not two. `CoalescesTo.no_cycle` then holds for cycles of every
length, by `Nat.lt_irrefl` on the transitive closure.

## Why `rerouted` carries no local carrier

A reroute moves an occurrence to a *different* session, and this ledger is one
channel's. An earlier revision made `rerouted` carry a replacement and subjected
it to the same "carrier is escrowed here" law as `coalesced`, which is
unsatisfiable for any genuine reroute: the carrier is by construction not in
this ledger. So `rerouted` records only the destination, and the obligation that
the payload reappears there is `ReroutedElsewhere` — stated here, dischargeable
only by `Plan.lean`, which holds every channel's ledger at once. That is a real
cross-ledger obligation, recorded rather than hidden inside a law this module
cannot check.

## Prefix laws, not step laws

`LedgerExtends` says one ledger is a later point of the same execution:
occurrences are only appended, a resolution once written is permanent, and a
cancellation request once made does not evaporate. The laws over it hold with no
responsiveness assumption at all, which is the point — §3 warns that "an
unrestricted infinite-pending execution may retain live escrow forever", and
they hold anyway.
-/

namespace Grass.Process

universe u s

/--
How an escrowed occurrence stopped being in flight.

`docs/PROCESS.md` §3 names these as "exhaustive competing resolution
transitions", with receive as the ordinary one. `channelClosed` is here because
§3 says separately that "ordinary close is distinct from endpoint death" and
`NetworkTransition` carries `channelClose` beside `channelDeath`; without it an
occurrence in flight at an ordinary close has no ending, and would either strand
live forever or have to be misrecorded as a death.

The payload rule is `Grass/Process/Network/Instance.lean`'s: a constructor
carries a payload exactly when nothing else determines it. A cancellation
acknowledgement happens at a declared point, and an endpoint death has a reason;
neither is recoverable from the ledger otherwise.
-/
inductive ChannelResolution (Occurrence : Type u) (Session : Type s) :
    Type (max u s)
  /-- The receiver consumed it. The ordinary ending. -/
  | received
  /-- A cancellation was *acknowledged*, at this point. Requesting one does not
  appear here. -/
  | cancelAcknowledged (reason : CancelReason)
  /-- It timed out. -/
  | timedOut
  /-- The session was closed in the ordinary way, which is not a death. -/
  | channelClosed
  /-- The sending incarnation died, for this reason. -/
  | senderDied (reason : ProcessDeathReason)
  /-- The receiving incarnation died, for this reason. -/
  | receiverDied (reason : ProcessDeathReason)
  /-- The session itself died. -/
  | channelDied
  /-- An explicitly modeled disposition dropped it. -/
  | dropped
  /-- It moved to this other session, where it is re-created as a fresh
  occurrence this ledger does not hold. -/
  | rerouted (destination : Session)
  /-- It merged into this occurrence of the same session, along with its fellow
  sources. -/
  | coalesced (carrier : Occurrence)

namespace ChannelResolution

variable {Occurrence : Type u} {Session : Type s}

/-- The occurrence *in this ledger* that carries this one's payload onward. -/
def carrier : ChannelResolution Occurrence Session → Option Occurrence
  | .coalesced carrier => some carrier
  | _ => none

/-- The other session this occurrence's payload moved to, if any. -/
def destination : ChannelResolution Occurrence Session → Option Session
  | .rerouted destination => some destination
  | _ => none

/--
An ending that consumes the payload here rather than passing it on.

`coalesced` passes it to another occurrence of this session; `rerouted` passes
it to another session. Everything else ends it.
-/
def IsTerminal (resolution : ChannelResolution Occurrence Session) : Prop :=
  resolution.carrier = none ∧ resolution.destination = none

theorem received_isTerminal :
    (ChannelResolution.received : ChannelResolution Occurrence Session).IsTerminal :=
  ⟨rfl, rfl⟩

theorem coalesced_not_terminal (carrier : Occurrence) :
    ¬ (ChannelResolution.coalesced (Session := Session) carrier).IsTerminal := by
  rintro ⟨noCarrier, _⟩
  exact absurd noCarrier (by simp [ChannelResolution.carrier])

theorem rerouted_not_terminal (destination : Session) :
    ¬ (ChannelResolution.rerouted (Occurrence := Occurrence) destination).IsTerminal := by
  rintro ⟨_, noDestination⟩
  exact absurd noDestination (by simp [ChannelResolution.destination])

end ChannelResolution

/--
The escrow held by one channel, at one point of an execution.

`created` is every occurrence this channel has ever escrowed, oldest first, and
`resolution` says how each one ended — `none` meaning it is still in flight.

`docs/PROCESS.md` §3 spells the plan-level object `ChannelEscrowLedger topology
Message`; that will be the per-edge family of these, and `Plan.lean` names it.
-/
structure EscrowLedger (Occurrence : Type u) (Session : Type s) where
  /-- Every occurrence ever escrowed here, oldest first. -/
  created : List Occurrence
  /-- Each occurrence's position in the monotone allocation history. -/
  rank : Occurrence → Nat
  /--
  And `rank` agrees with `created`'s order, so there is one order and not two.

  Strict, so it also gives duplicate-freedom: an occurrence escrowed twice would
  be a fabricated identity, and here it would need a rank strictly below itself.
  -/
  rankOrdersCreated : (created.map rank).Pairwise (· < ·)
  /-- How each occurrence ended, or `none` while it is in flight. -/
  resolution : Occurrence → Option (ChannelResolution Occurrence Session)
  /-- Nothing is resolved that was never escrowed. -/
  noFabrication : ∀ occurrence, (resolution occurrence).isSome = true →
    occurrence ∈ created
  /--
  **A coalesce names a real carrier, strictly later than its source.**

  The law that makes `coalesced` an onward transfer rather than a drop. See the
  module note: irreflexivity alone admits cycles, in which every payload is
  "passed on" and none lands.
  -/
  coalesceCarrierLater : ∀ occurrence carrier,
    resolution occurrence = some (.coalesced carrier) →
    carrier ∈ created ∧ rank occurrence < rank carrier
  /-- A cancellation has been requested for these. Says nothing about escrow. -/
  cancelRequested : Occurrence → Bool
  /--
  An acknowledgement acknowledges something.

  `docs/PROCESS.md` §3 calls a cancellation request an affine occurrence, so an
  acknowledgement of a request that was never made is a fabricated ending. Note
  what this does *not* say: it constrains the acknowledgement, not the escrow,
  so a requested-but-unacknowledged cancellation still leaves the payload in
  flight.
  -/
  acknowledgedWasRequested : ∀ occurrence reason,
    resolution occurrence = some (.cancelAcknowledged reason) →
    cancelRequested occurrence = true

namespace EscrowLedger

variable {Occurrence : Type u} {Session : Type s} (ledger : EscrowLedger Occurrence Session)

/--
The ledger of a session that has never escrowed anything.

Every law is vacuous here, which is the point: a network holds one of these for
each session before its first send, and a plan should not have to construct the
proofs to say "nothing in flight".
-/
def empty : EscrowLedger Occurrence Session where
  created := []
  rank := fun _ => 0
  rankOrdersCreated := by simp
  resolution := fun _ => none
  noFabrication := by simp
  coalesceCarrierLater := by simp
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by simp

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
**At most one recorded ending.**

A projection, not an assumption: `resolution` is a function. See the module note
for what this is *not* — it is the recording half of §3's affine resolve token,
and the once-consumption half needs the transition family.
-/
theorem atMostOneRecordedEnding {occurrence : Occurrence}
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

/-! ## Coalescing cannot go in circles -/

/-- One occurrence's payload reaches another by one or more coalesces. -/
inductive CoalescesTo {Occurrence : Type u} {Session : Type s}
    (ledger : EscrowLedger Occurrence Session) : Occurrence → Occurrence → Prop
  /-- One coalesce. -/
  | step {source carrier : Occurrence}
      (merged : ledger.resolution source = some (.coalesced carrier)) :
      CoalescesTo ledger source carrier
  /-- And onward. -/
  | trans {source middle target : Occurrence}
      (first : CoalescesTo ledger source middle)
      (rest : CoalescesTo ledger middle target) :
      CoalescesTo ledger source target

namespace CoalescesTo

variable {Occurrence : Type u} {Session : Type s} {ledger : EscrowLedger Occurrence Session}

/-- Rank strictly increases along every coalesce path. -/
theorem rank_increases {source target : Occurrence}
    (reaches : CoalescesTo ledger source target) :
    ledger.rank source < ledger.rank target := by
  induction reaches with
  | step merged => exact (ledger.coalesceCarrierLater _ _ merged).2
  | trans _ _ firstRank restRank => exact Nat.lt_trans firstRank restRank

/--
**No coalesce cycle, of any length.**

The law an irreflexivity condition could not give. Without it two occurrences
may merge into each other, or a chain may close, and every field of the ledger
still discharges while both payloads land nowhere — a ledger that reports itself
in order and has lost everything in the cycle.
-/
theorem no_cycle {occurrence : Occurrence}
    (loops : CoalescesTo ledger occurrence occurrence) : False :=
  Nat.lt_irrefl _ loops.rank_increases

end CoalescesTo

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

variable {Occurrence : Type u} {Session : Type s} (ledger : EscrowLedger Occurrence Session)

/--
**Accounting.**

Every escrowed occurrence is either still in flight or has ended, and the two
counts add to the number ever created.

A counting identity about *one* ledger, and this docstring is careful not to
claim more: it uses `created` and `resolution` and none of the other fields, so
"nothing is invented" is `noFabrication`'s and not this theorem's, and what is
counted is identities rather than the resources §3 says travel with them.
§3's *prefix* conservation is `settled_monotone` and `created_monotone` below.
-/
theorem accounting :
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

`docs/PROCESS.md` §3 requires this, because a request that reclaimed the escrow
would lose the payload of a message whose cancellation later loses its race with
delivery.

This theorem is the projection `Outstanding` already carries, and it is honest
to say so: it would still prove if a field tying `cancelRequested` to
`resolution` were added — it would merely become vacuous. What actually enforces
the independence is `Tests/Process/EscrowFixtures.lean`, which builds a ledger
with a cancellation requested against an outstanding occurrence and stops
elaborating the moment such a field exists. An earlier revision of this
docstring claimed the theorem itself was the guard; it is not.
-/
theorem cancel_request_leaves_escrow (occurrence : Occurrence)
    (inFlight : ledger.Outstanding occurrence)
    (_requested : ledger.cancelRequested occurrence = true) :
    ledger.resolution occurrence = none :=
  inFlight.2

/--
The cross-ledger obligation a reroute creates.

`rerouted destination` says the payload left this channel; it does not and
cannot say it arrived. This predicate names what a plan holding every channel's
ledger must prove: for each rerouted occurrence, the destination session escrows
something carrying it.

Stated here so the obligation is written down at the point it is created rather
than remembered at the point it could be discharged.
-/
def ReroutedElsewhere (landsAt : Session → Occurrence → Prop) : Prop :=
  ∀ occurrence destination,
    ledger.resolution occurrence = some (.rerouted destination) →
    ∃ arrival, landsAt destination arrival

end EscrowLedger

/--
**One step resolved at most this occurrence.**

`LedgerExtends` below says nothing was *erased*: a resolution once written is
permanent, a cancellation request does not evaporate, occurrences are only
appended. It says nothing about what was *added* — so a step that legally
resolves one occurrence may, in the same move, append an unrelated occurrence and
resolve it too, and no field of any constructor mentions it.

That is not hypothetical. `Tests/Process/RerouteFixtures.lean` builds a `drop`
discharging every field `ProcessPlan.ResolvesEscrow` had, which appends a second
occurrence and resolves it `.rerouted` to a session whose ledger the step never
touches — taking a network satisfying `LogicalProcessNetworkCore.ReroutesLand` to
one that does not. That clause is the sixth of `WellFormed`, and it is not
preserved without this. `docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.87.

Stated as "nothing *else*" rather than "exactly this" because the constructors
already say what happens to their own occurrence, each in its own way — a
delivery resolves `.received`, a reroute `.rerouted`, a send resolves nothing at
all — and a second statement of it would be a second chance to disagree.
-/
def ResolvesNothingElse {Occurrence : Type u} {Session : Type s}
    (earlier later : EscrowLedger Occurrence Session) (occurrence : Occurrence) : Prop :=
  ∀ other, other ≠ occurrence → later.resolution other = earlier.resolution other

/--
A step that touches no ledger resolves nothing else in it.

The shape every off-session discharge takes: the two ledgers are equal, so every
occurrence reads the same.
-/
theorem resolvesNothingElse_of_eq {Occurrence : Type u} {Session : Type s}
    {earlier later : EscrowLedger Occurrence Session} {occurrence : Occurrence}
    (same : earlier = later) : ResolvesNothingElse earlier later occurrence :=
  fun _ _ => same ▸ rfl

/--
One ledger is a later point of the same execution than another.

The prefix relation `docs/PROCESS.md` §3's unconditional laws are stated over.
-/
structure LedgerExtends {Occurrence : Type u} {Session : Type s}
    (earlier later : EscrowLedger Occurrence Session) where
  /-- Occurrences are only appended. -/
  createdPrefix : earlier.created.IsPrefix later.created
  /-- A resolution, once written, is never rewritten or erased. -/
  resolutionPermanent : ∀ occurrence resolution,
    earlier.resolution occurrence = some resolution →
    later.resolution occurrence = some resolution
  /--
  A cancellation request, once made, does not evaporate.

  Without this an outstanding request disappears with no acknowledgement, no
  timeout and no record, which is `docs/FOUNDATION.md` law 7 — §3 calls the
  request an affine occurrence, and an affine thing that vanishes was not
  affine.
  -/
  cancelRequestMonotone : ∀ occurrence,
    earlier.cancelRequested occurrence = true →
    later.cancelRequested occurrence = true

namespace LedgerExtends

variable {Occurrence : Type u} {Session : Type s} {earlier later : EscrowLedger Occurrence Session}

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
-/
theorem noLoss (extension : LedgerExtends earlier later) {occurrence : Occurrence}
    (inFlight : earlier.Outstanding occurrence) :
    later.Outstanding occurrence ∨ later.Resolved occurrence = true := by
  have escrowed := extension.created_preserved inFlight.1
  cases ending : later.resolution occurrence with
  | none => exact Or.inl ⟨escrowed, ending⟩
  | some _ => exact Or.inr (by simp [EscrowLedger.Resolved, ending])

/-- **The prefix half of conservation: what was settled stays settled.** -/
theorem settled_monotone (extension : LedgerExtends earlier later)
    {occurrence : Occurrence} (wasSettled : occurrence ∈ earlier.settled) :
    occurrence ∈ later.settled := by
  have escrowed := (List.mem_filter.mp wasSettled).1
  have resolved := (List.mem_filter.mp wasSettled).2
  refine List.mem_filter.mpr ⟨extension.created_preserved escrowed, ?_⟩
  cases ending : earlier.resolution occurrence with
  | none =>
    rw [EscrowLedger.Resolved, ending] at resolved
    exact absurd resolved (by simp)
  | some _ =>
    rw [EscrowLedger.Resolved, extension.resolvedStaysResolved ending]
    rfl

/-- And what was escrowed stays escrowed, so neither count can shrink. -/
theorem created_monotone (extension : LedgerExtends earlier later) :
    earlier.created.length ≤ later.created.length :=
  extension.createdPrefix.length_le

/-- Extension is reflexive: a ledger is a later point of itself. -/
theorem refl (ledger : EscrowLedger Occurrence Session) : LedgerExtends ledger ledger where
  createdPrefix := List.prefix_refl _
  resolutionPermanent := fun _ _ ended => ended
  cancelRequestMonotone := fun _ requested => requested

/-- And transitive, so the laws hold across a whole execution, not one step. -/
theorem trans {middle : EscrowLedger Occurrence Session}
    (first : LedgerExtends earlier middle) (second : LedgerExtends middle later) :
    LedgerExtends earlier later where
  createdPrefix := first.createdPrefix.trans second.createdPrefix
  resolutionPermanent := fun occurrence resolution ended =>
    second.resolutionPermanent occurrence resolution
      (first.resolutionPermanent occurrence resolution ended)
  cancelRequestMonotone := fun occurrence requested =>
    second.cancelRequestMonotone occurrence
      (first.cancelRequestMonotone occurrence requested)

end LedgerExtends

end Grass.Process
