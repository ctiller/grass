import Tests.Process.CloseFixtures

/-!
# A channel that merges payloads rather than collapsing equal ones

`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.130, closing what §10.127 recorded as
owed.

`agent-bus` ruling `g-design:83` generalised `ResolvesEscrow`'s per-source
`carrier.1 = occurrence.1` into `ProcessPlan.coalescing`, because the equality
made latest-wins and folding channels unconstructible at every plan. §10.127
landed that generalisation and recorded honestly that the corpus instantiated the
new field at `ProcessPlan.exactDedup` and nowhere else — a field with one
instantiation is the generalisation in name only, which is the shape this ledger
keeps refusing.

This file is the missing instantiation, and building it found that §10.127's own
policy fixture was worse than under-exercised: it was **unsatisfiable**. See
§10.130 and `latestWins_is_unsatisfiable` below.

## Why a merge takes two steps

`ResolvesEscrow.resolvesNothingElse` lets a step resolve exactly the occurrence
it names, so a merge of two sources is two coalesces into one carrier — which is
what `Tests/Process/CloseFixtures.lean`'s `bothMerged` already does with equal
payloads. `carrierIsPermitted` then reads the source family off the *after*
ledger of each step, so the two steps see different families: the first sees the
source it just merged, the second sees both.

That ordering is what makes the policy visible. The carrier here holds
`otherPayload`, so:

* the first step merges `loud`, which carries `otherPayload`. `exactDedup` would
  accept this one — every source agrees with the carrier.
* the second step merges `escrowed`, which carries `payload`. Now the family is
  `[escrowed, loud]` and its members disagree. `exactDedup` refuses it and
  `keepsOnePayload` does not, and that difference is
  `the_merge_is_refused_by_dedup` below.
-/

namespace Grass.Process.Tests.Merge

open Grass.Process
open Grass.Process.Tests
open Grass.Process.Tests.World (ServerWorld)
open Grass.Process.Tests.Channel (wire)
open Grass.Process.Tests.Transition (serverPlan payload escrowed)

/-! ## The policy, and the one §10.127 got wrong -/

/--
**A merge may keep any one of its sources' payloads.**

The policy `ProcessPlan.exactDedup` refuses: the carrier agrees with *some*
source rather than with every source. A folding channel would relate the family
to a computed carrier instead; a latest-wins channel would additionally pin
*which* source, which needs an order this layer does not give the relation.
Keeping one is the weakest policy that is not deduplication, which makes it the
right one to exhibit.
-/
def keepsOnePayload (sources : List (EdgeOccurrence serverTopology World.serverMessage ()))
    (carrier : EdgeOccurrence serverTopology World.serverMessage ()) : Prop :=
  ∃ source ∈ sources, source.1 = carrier.1

/--
**And the policy §10.127 first offered can be satisfied by no coalesce at any
plan.**

That policy was `latestWins sources carrier := carrier ∈ sources`, in
`Tests/Process/CloseFixtures.lean`, and it came with a proof that it admits a
family `exactDedup` refuses. Both facts are true and the pair proves less
than it looks, because no `ResolvesEscrow` can ever hand that predicate a family
containing its own carrier: `carrierIsPermitted` takes the sources to be exactly
those the after-ledger resolves into the carrier, and
`EscrowLedger.coalesceCarrierLater` requires every such source to have rank
*strictly below* the carrier's. A carrier of rank strictly below its own rank
does not exist.

So the fixture that was supposed to show the generalisation had content was
itself a predicate no plan can meet — the failure it was written to rule out, one
level up. `keepsOnePayload` is the replacement, and `mergingPlan` instantiates
it.
-/
theorem latestWins_is_unsatisfiable
    (ledger : EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()))
    (carrier : EdgeOccurrence serverTopology World.serverMessage ())
    (isSource : ledger.resolution carrier = some (.coalesced carrier)) : False := by
  have later := (ledger.coalesceCarrierLater carrier carrier isSource).2
  exact absurd later (Nat.lt_irrefl _)

/-! ## A second plan over the same topology -/

/--
The same graph, channels and contracts as `serverPlan`, with one field changed.

A plan is a topology, a message family, per-edge steps and contracts, and its
policies. Only the coalescing policy differs here, so every world, occurrence and
ledger the other fixtures build is a world of this plan too — which is what makes
the comparison a comparison rather than two unrelated stories.
-/
noncomputable def mergingPlan : ProcessPlan graphRegistry fixtureBoundary World.NoObligations :=
  { serverPlan with coalescing := fun _ => keepsOnePayload }

theorem mergingPlan_world : mergingPlan.LogicalProcessNetwork = ServerWorld := rfl

/-! ## Two payloads that disagree -/

/-- A second, different payload. -/
def otherPayload : World.serverMessage () := ⟨99⟩

theorem the_payloads_differ : otherPayload ≠ payload := by
  intro same
  have counts : (99 : Nat) = 7 := congrArg (fun message => message.down) same
  exact absurd counts (by decide)

/-- The occurrence carrying it. -/
def loud : EdgeOccurrence serverTopology World.serverMessage () :=
  ⟨otherPayload, ⟨wire, { id := ⟨.messageOccurrence, 8⟩, isMessage := rfl }⟩⟩

/-- And the carrier the merge keeps, which carries `otherPayload` too. -/
def mergeCarrier : EdgeOccurrence serverTopology World.serverMessage () :=
  ⟨otherPayload, ⟨wire, { id := ⟨.messageOccurrence, 9⟩, isMessage := rfl }⟩⟩

theorem loud_ne_escrowed : loud ≠ escrowed := by
  intro same
  have ids : (8 : Nat) = 0 := congrArg (fun occurrence => occurrence.2.2.id.carrier) same
  exact absurd ids (by decide)

theorem carrier_ne_escrowed : mergeCarrier ≠ escrowed := by
  intro same
  have ids : (9 : Nat) = 0 := congrArg (fun occurrence => occurrence.2.2.id.carrier) same
  exact absurd ids (by decide)

theorem carrier_ne_loud : mergeCarrier ≠ loud := by
  intro same
  have ids : (9 : Nat) = 8 := congrArg (fun occurrence => occurrence.2.2.id.carrier) same
  exact absurd ids (by decide)

/-! ## The three ledgers a two-source merge passes through -/

open Classical in
/-- Both messages in flight, neither resolved. -/
noncomputable def bothLoud :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed, loud]
  rank := fun occurrence => occurrence.2.2.id.carrier
  rankOrdersCreated := by decide
  resolution := fun _ => none
  noFabrication := by simp
  coalesceCarrierLater := by simp
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by simp

open Classical in
/-- The carrier created, with `loud` merged into it. -/
noncomputable def firstMerged :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed, loud, mergeCarrier]
  rank := fun occurrence => occurrence.2.2.id.carrier
  rankOrdersCreated := by decide
  resolution := fun occurrence =>
    if occurrence = loud then some (.coalesced mergeCarrier) else none
  noFabrication := by
    intro occurrence resolved
    by_cases isLoud : occurrence = loud
    · simp [isLoud]
    · simp [isLoud] at resolved
  coalesceCarrierLater := by
    intro occurrence carrier isMerge
    by_cases isLoud : occurrence = loud
    · subst isLoud
      rw [if_pos rfl] at isMerge
      cases isMerge
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by decide⟩
    · rw [if_neg isLoud] at isMerge
      cases isMerge
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by
    intro occurrence reason acknowledged
    by_cases isLoud : occurrence = loud
    · simp [isLoud] at acknowledged
    · simp [isLoud] at acknowledged

open Classical in
/-- And with `escrowed` merged into it too, which is the step this file is for. -/
noncomputable def bothMergedLoudly :
    EscrowLedger (EdgeOccurrence serverTopology World.serverMessage ())
      (serverTopology.ChannelId ()) where
  created := [escrowed, loud, mergeCarrier]
  rank := fun occurrence => occurrence.2.2.id.carrier
  rankOrdersCreated := by decide
  resolution := fun occurrence =>
    if occurrence = loud then some (.coalesced mergeCarrier)
    else if occurrence = escrowed then some (.coalesced mergeCarrier) else none
  noFabrication := by
    intro occurrence resolved
    by_cases isLoud : occurrence = loud
    · simp [isLoud]
    · by_cases isFirst : occurrence = escrowed
      · simp [isFirst]
      · simp [isLoud, isFirst] at resolved
  coalesceCarrierLater := by
    intro occurrence carrier isMerge
    by_cases isLoud : occurrence = loud
    · subst isLoud
      rw [if_pos rfl] at isMerge
      cases isMerge
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by decide⟩
    · rw [if_neg isLoud] at isMerge
      by_cases isFirst : occurrence = escrowed
      · subst isFirst
        rw [if_pos rfl] at isMerge
        cases isMerge
        exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by decide⟩
      · rw [if_neg isFirst] at isMerge
        cases isMerge
  cancelRequested := fun _ => false
  acknowledgedWasRequested := by
    intro occurrence reason acknowledged
    by_cases isLoud : occurrence = loud
    · simp [isLoud] at acknowledged
    · by_cases isFirst : occurrence = escrowed
      · simp [isFirst] at acknowledged
      · simp [isLoud, isFirst] at acknowledged

open Classical in
theorem firstMerged_loud : firstMerged.resolution loud = some (.coalesced mergeCarrier) := by
  show (if loud = loud then some (ChannelResolution.coalesced mergeCarrier) else none)
    = some (.coalesced mergeCarrier)
  rw [if_pos rfl]

open Classical in
theorem firstMerged_other {occurrence : EdgeOccurrence serverTopology World.serverMessage ()}
    (notLoud : occurrence ≠ loud) : firstMerged.resolution occurrence = none := by
  show (if occurrence = loud then some (ChannelResolution.coalesced mergeCarrier) else none)
    = none
  rw [if_neg notLoud]

open Classical in
theorem bothMergedLoudly_loud :
    bothMergedLoudly.resolution loud = some (.coalesced mergeCarrier) := by
  show (if loud = loud then some (ChannelResolution.coalesced mergeCarrier)
    else if loud = escrowed then some (ChannelResolution.coalesced mergeCarrier) else none)
      = some (.coalesced mergeCarrier)
  rw [if_pos rfl]

open Classical in
theorem bothMergedLoudly_first :
    bothMergedLoudly.resolution escrowed = some (.coalesced mergeCarrier) := by
  show (if escrowed = loud then some (ChannelResolution.coalesced mergeCarrier)
    else if escrowed = escrowed then some (ChannelResolution.coalesced mergeCarrier) else none)
      = some (.coalesced mergeCarrier)
  rw [if_neg (fun same => loud_ne_escrowed same.symm), if_pos rfl]

open Classical in
theorem bothMergedLoudly_other
    {occurrence : EdgeOccurrence serverTopology World.serverMessage ()}
    (notLoud : occurrence ≠ loud) (notFirst : occurrence ≠ escrowed) :
    bothMergedLoudly.resolution occurrence = none := by
  show (if occurrence = loud then some (ChannelResolution.coalesced mergeCarrier)
    else if occurrence = escrowed then some (ChannelResolution.coalesced mergeCarrier)
    else none) = none
  rw [if_neg notLoud, if_neg notFirst]

/-! ## The worlds -/

open Classical in
noncomputable def bothInFlight : ServerWorld :=
  { World.withRoot with
      inFlight := fun _ session => if session = wire then bothLoud else EscrowLedger.empty }

open Classical in
theorem bothInFlight_wire : bothInFlight.inFlight () wire = bothLoud := by
  show (if wire = wire then bothLoud else EscrowLedger.empty) = bothLoud
  rw [if_pos rfl]

open Classical in
noncomputable def afterFirstMerge : ServerWorld :=
  { World.withRoot with
      inFlight := fun _ session => if session = wire then firstMerged else EscrowLedger.empty }

open Classical in
theorem afterFirstMerge_wire : afterFirstMerge.inFlight () wire = firstMerged := by
  show (if wire = wire then firstMerged else EscrowLedger.empty) = firstMerged
  rw [if_pos rfl]

open Classical in
noncomputable def afterBothMerges : ServerWorld :=
  { World.withRoot with
      inFlight := fun _ session =>
        if session = wire then bothMergedLoudly else EscrowLedger.empty }

open Classical in
theorem afterBothMerges_wire : afterBothMerges.inFlight () wire = bothMergedLoudly := by
  show (if wire = wire then bothMergedLoudly else EscrowLedger.empty) = bothMergedLoudly
  rw [if_pos rfl]

/-! ## The merge -/

theorem escrowed_is_outstanding : bothLoud.Outstanding escrowed :=
  ⟨List.mem_cons_self, rfl⟩

theorem loud_is_outstanding : bothLoud.Outstanding loud :=
  ⟨List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩

open Classical in
/--
**A merge of two payloads that disagree, in one step.**

The family is `[escrowed, loud]`; `escrowed` carries `payload` and the carrier
carries `otherPayload`, so the family's members disagree about what the carrier
should hold. `mergingPlan.coalescing` is `keepsOnePayload`, which asks only that
*some* source agree with the carrier, and `loud` does.

`serverPlan` could not take this step, and `serverPlan_refuses_it` below is that.
The difference between the two plans is one field.
-/
theorem the_merge_that_keeps_one_payload :
    mergingPlan.Coalesces bothInFlight afterBothMerges () wire [escrowed, loud]
      mergeCarrier where
  sourcesNonempty := by simp
  sourcesOnItsSession := by
    intro source inList
    rcases List.mem_cons.mp inList with isFirst | rest
    · rw [isFirst]; rfl
    · rw [List.mem_singleton.mp rest]; rfl
  wereOutstanding := by
    intro source inList
    rw [bothInFlight_wire]
    rcases List.mem_cons.mp inList with isFirst | rest
    · rw [isFirst]; exact escrowed_is_outstanding
    · rw [List.mem_singleton.mp rest]; exact loud_is_outstanding
  nowResolved := by
    intro source inList
    rw [afterBothMerges_wire]
    rcases List.mem_cons.mp inList with isFirst | rest
    · rw [isFirst]; exact bothMergedLoudly_first
    · rw [List.mem_singleton.mp rest]; exact bothMergedLoudly_loud
  resolvesNothingElse := by
    intro other notSource
    have notFirst : other ≠ escrowed :=
      fun same => notSource (by rw [same]; exact List.mem_cons_self)
    have notLoud : other ≠ loud :=
      fun same => notSource (by rw [same]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [afterBothMerges_wire, bothMergedLoudly_other notLoud notFirst, bothInFlight_wire]
    rfl
  consumesExactly := by
    intro other resolved
    rw [afterBothMerges_wire] at resolved
    by_cases isFirst : other = escrowed
    · rw [isFirst]; exact List.mem_cons_self
    · by_cases isLoud : other = loud
      · rw [isLoud]; exact List.mem_cons_of_mem _ List.mem_cons_self
      · rw [bothMergedLoudly_other isLoud isFirst] at resolved
        exact absurd resolved (by intro equal; cases equal)
  ledgerExtends := by
    rw [bothInFlight_wire, afterBothMerges_wire]
    exact
      { createdPrefix := ⟨[mergeCarrier], rfl⟩
        resolutionPermanent := by
          intro occurrence resolution ended
          exact absurd ended (by intro equal; cases equal)
        cancelRequestMonotone := by
          intro occurrence requested
          exact absurd requested (by intro equal; cases equal) }
  carrierOnItsSession := rfl
  carrierIsOutstanding := by
    rw [afterBothMerges_wire]
    exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      bothMergedLoudly_other carrier_ne_loud carrier_ne_escrowed⟩
  permitted := ⟨loud, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  createsOnlyTheCarrier := by
    intro other held fresh
    have inList : other ∈ (afterBothMerges.inFlight () wire).created := held
    rw [afterBothMerges_wire] at inList
    have three : other ∈ [escrowed, loud, mergeCarrier] := inList
    rcases List.mem_cons.mp three with isFirst | rest
    · exact absurd (by rw [isFirst, bothInFlight_wire]; exact List.mem_cons_self) fresh
    · rcases List.mem_cons.mp rest with isSecond | last
      · refine absurd ?_ fresh
        rw [isSecond, bothInFlight_wire]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_singleton.mp last
  createdIdentityIsFresh := by
    intro other old
    have oldList : other ∈ (bothInFlight.inFlight () wire).created := old
    rw [bothInFlight_wire] at oldList
    have two : other ∈ [escrowed, loud] := oldList
    rcases List.mem_cons.mp two with isFirst | rest
    · rw [isFirst]
      intro same
      have ids : (0 : Nat) = 9 := congrArg (fun nominal => nominal.carrier) same
      exact absurd ids (by decide)
    · rw [List.mem_singleton.mp rest]
      intro same
      have ids : (8 : Nat) = 9 := congrArg (fun nominal => nominal.carrier) same
      exact absurd ids (by decide)
  requestsNothing := by
    show RequestsNothing (bothInFlight.inFlight () wire) (afterBothMerges.inFlight () wire)
    rw [bothInFlight_wire, afterBothMerges_wire]
    exact fun _ => rfl
  scope := by
    intro fragment outside
    cases fragment with
    | escrow edge session =>
      have sameEdge : edge = () := rfl
      subst sameEdge
      have notWire : session ≠ wire := by
        intro isWire
        subst isWire
        exact outside rfl
      show (if session = wire then bothLoud else EscrowLedger.empty)
        = (if session = wire then bothMergedLoudly else EscrowLedger.empty)
      rw [if_neg notWire, if_neg notWire]
    | _ => rfl

/--
**And `ProcessPlan.exactDedup` refuses exactly that family.**

The same source family and carrier a real merge produced, put to the other
policy. This is the difference `agent-bus` ruling `g-design:83` is about, at the
family a `Coalesces` actually names rather than at a list chosen to make a point.
-/
theorem the_merge_is_refused_by_dedup :
    ¬ exactDedup [escrowed, loud] mergeCarrier := by
  intro dedup
  have payloads := dedup escrowed List.mem_cons_self
  have counts : (7 : Nat) = 99 := congrArg (fun message => message.down) payloads
  exact absurd counts (by decide)

/--
**So `serverPlan` could not have taken this step**, which is what makes the
policy a property of the channel rather than of the layer.

`Coalesces.permitted` is the only field that differs in what it asks of the two
plans; every other field of the step above would be discharged verbatim at
`serverPlan`.
-/
theorem serverPlan_refuses_it
    (step : serverPlan.Coalesces bothInFlight afterBothMerges () wire [escrowed, loud]
      mergeCarrier) : False :=
  the_merge_is_refused_by_dedup step.permitted

end Grass.Process.Tests.Merge
