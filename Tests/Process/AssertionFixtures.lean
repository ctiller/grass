import Grass.Process.Network.Assertion
import Tests.Process.M2GraphFixtures

/-!
# The footprint is a bound, not a label

`Grass/Process/Network/Assertion.lean` makes two claims that a module cannot
check about itself, because they are claims about what its types *reject*. This
fixture checks them.

* `framed` bounds what an assertion may read. `understated_footprint_impossible`
  is that: no assertion with an empty footprint can read `acceptCount`.
* `agreesGlue` makes the bound mean something. `fixtureAgreement` discharges it,
  and `separate_fragments_are_independent` shows the payoff — two worlds
  agreeing on one fragment and differing on another, which the degenerate
  equality agreement the module note describes could not exhibit.

It also pins the two compositions `Grass/Process/Network/Channel.lean` has to
write and would otherwise discover were unwritable:

* `ReceiverPre * Escrow` — `receiver_pre_separate_from_escrow`. This is why
  `escrow` and `session` are separate fragments; a single `channel` constructor
  would make these two overlap and the conjunction unformable.
* the negative direction — `same_region_not_separate`, so that `Separate` is
  known not to be universally true.

The topology is `Tests/Process/M2GraphFixtures.lean`'s, reused rather than
rebuilt, so a change to the topology surface breaks this file too.

## Why this world has one component per fragment

`FixtureWorld` below is a product with exactly one field per `NetworkFragment`
family, and the instance and channel fields are *functions of their index*. That
is not incidental convenience: it is what makes `agreesGlue` easy to
discharge here, since a product mixes componentwise. It is not what `agreesGlue`
*demands* — `leakyAgreement` below satisfies the law over the same world without
any such correspondence, which is §10.137. An earlier draft of this fixture had a single
`listenerCursor : Nat` read by every `instanceState` fragment, which made two
assertions about different slots `Separate` while reading the same field —
exactly the aliasing `agreesGlue` now forbids.
-/

namespace Grass.Process.Tests.NetworkAssertions

open Grass.Process
open Grass.Process.Tests

/-- Two incarnations of the listener, to have distinct instance fragments. -/
@[reducible] def listenerRef (generation : Nat) :
    serverTopology.ProcessRef .listener where
  instanceId := ()
  generation := ⟨.processGeneration, generation⟩
  isGeneration := rfl

/-- One session on the one channel edge. -/
@[reducible] def sessionOn (generation : Nat) : serverTopology.ChannelId () where
  sender := listenerRef 0
  receiver := connectionSeven 0
  epoch := ⟨.channelEpoch, generation⟩
  isEpoch := rfl

/--
A concrete world for the fixture topology: one component per fragment family.

The instance and channel components are functions of their index, so that
`instanceState kind slot` reads *that* slot and no other. See the module note on
why this shape is forced rather than chosen.
-/
structure FixtureWorld where
  /-- `region .routeTable`. -/
  routeTable : List String
  /-- `region .acceptCount`. -/
  acceptCount : Nat
  /-- `instanceState kind slot`, per instance slot. -/
  cursor : (kind : Role) → serverTopology.InstanceId kind → Nat
  /-- `escrow () session`: the payload in flight, if any. -/
  escrow : (edge : serverTopology.ChannelKind) →
    serverTopology.ChannelId edge → Option Nat
  /-- `session () session`: the receiver's position in that session. -/
  received : (edge : serverTopology.ChannelKind) →
    serverTopology.ChannelId edge → Nat
  /-- `obligations`. -/
  obligations : Nat
  /-- `observations`: what has been committed. -/
  observations : List String
  /-- `pending`: what processes have produced and no commit has published. -/
  pending : List String
  /-- `nominals`: how much of the monotone history has been consumed. -/
  nominals : Nat

/-- Agreement, fragment by fragment: each fragment reads exactly its component. -/
def fixtureAgrees : NetworkFragment serverTopology →
    FixtureWorld → FixtureWorld → Prop
  | .instanceState kind slot, left, right => left.cursor kind slot = right.cursor kind slot
  | .region .routeTable, left, right => left.routeTable = right.routeTable
  | .region .acceptCount, left, right => left.acceptCount = right.acceptCount
  | .escrow edge session, left, right => left.escrow edge session = right.escrow edge session
  | .session edge session, left, right =>
      left.received edge session = right.received edge session
  | .obligations, left, right => left.obligations = right.obligations
  | .observations, left, right => left.observations = right.observations
  | .pending, left, right => left.pending = right.pending
  | .nominals, left, right => left.nominals = right.nominals

open Classical in
/--
The agreement, with all four laws.

`agreesGlue` is the interesting one and it is discharged by construction: the
mixed world takes each component from `left` or from `right` according to
whether the fragment reading it is inside the split. That is only writable
because the world is a product over the fragments, which is the point of the
law.

`inside` is an arbitrary predicate, so the construction decides it classically.
The library carries no such dependency — `agreesGlue` is a hypothesis there, not
a proof — and it is the *world supplier* that pays, which is the right place.
-/
noncomputable def fixtureAgreement : WorldAgreement serverTopology FixtureWorld where
  Agrees := fixtureAgrees
  agreesRefl := by
    intro fragment _
    cases fragment with
    | region region => cases region <;> rfl
    | _ => rfl
  agreesSymm := by
    intro fragment left right agrees
    cases fragment with
    | region region => cases region <;> exact agrees.symm
    | _ => exact agrees.symm
  agreesTrans := by
    intro fragment a b c ab bc
    cases fragment with
    | region region => cases region <;> exact ab.trans bc
    | _ => exact ab.trans bc
  agreesGlue := by
    intro inside left right
    refine ⟨{
      routeTable := if inside (.region .routeTable) then left.routeTable else right.routeTable
      acceptCount := if inside (.region .acceptCount) then left.acceptCount else right.acceptCount
      cursor := fun kind slot =>
        if inside (.instanceState kind slot) then left.cursor kind slot
        else right.cursor kind slot
      escrow := fun edge session =>
        if inside (.escrow edge session) then left.escrow edge session
        else right.escrow edge session
      received := fun edge session =>
        if inside (.session edge session) then left.received edge session
        else right.received edge session
      obligations := if inside .obligations then left.obligations else right.obligations
      observations := if inside .observations then left.observations else right.observations
      pending := if inside .pending then left.pending else right.pending
      nominals := if inside .nominals then left.nominals else right.nominals }, ?_, ?_⟩
    · intro fragment member
      cases fragment with
      | region region => cases region <;> simp [fixtureAgrees, member]
      | _ => simp [fixtureAgrees, member]
    · intro fragment member
      cases fragment with
      | region region => cases region <;> simp [fixtureAgrees, member]
      | _ => simp [fixtureAgrees, member]

/-- The empty world. -/
def quiet : FixtureWorld where
  routeTable := []
  acceptCount := 0
  cursor := fun _ _ => 0
  escrow := fun _ _ => none
  received := fun _ _ => 0
  obligations := 0
  observations := []
  pending := []
  nominals := 0

/-- After: one connection accepted. The table is untouched. -/
def afterAccept : FixtureWorld := { quiet with acceptCount := 1 }

/--
**The payoff of `agreesGlue`, exhibited.**

Two worlds that agree on the route table and differ on the accept count. Under
the degenerate equality agreement the module note describes, no such pair could
exist, and `Separate` would carry no information at all.
-/
theorem separate_fragments_are_independent :
    fixtureAgreement.Agrees (.region .routeTable) quiet afterAccept ∧
      ¬ fixtureAgreement.Agrees (.region .acceptCount) quiet afterAccept := by
  refine ⟨rfl, ?_⟩
  intro agrees
  exact Nat.zero_ne_one agrees

/-! ## Two assertions, over disjoint regions -/

/-- The route table is empty. Reads one region and nothing else. -/
def routeTableEmpty : NetworkAssertion fixtureAgreement where
  holds := fun world => world.routeTable = []
  footprint := fun fragment => fragment = .region .routeTable
  framed := by
    intro left right agrees
    have same : left.routeTable = right.routeTable := agrees _ rfl
    rw [same]

/-- Some connection has been accepted. Reads the other region. -/
def acceptedSomething : NetworkAssertion fixtureAgreement where
  holds := fun world => 0 < world.acceptCount
  footprint := fun fragment => fragment = .region .acceptCount
  framed := by
    intro left right agrees
    have same : left.acceptCount = right.acceptCount := agrees _ rfl
    rw [same]

/-- They read different regions, so they are separate. -/
theorem regions_are_separate :
    NetworkAssertion.Separate routeTableEmpty acceptedSomething := by
  rintro fragment (rfl : fragment = _) (overlap : _ = _)
  simp at overlap

/--
**And `Separate` is not universally true.**

The negative half. Without it, `regions_are_separate` would be consistent with a
`Separate` that every pair satisfied, and the separating conjunction would be an
ordinary one wearing a hat.
-/
theorem same_region_not_separate :
    ¬ NetworkAssertion.Separate acceptedSomething acceptedSomething := by
  intro separate
  exact separate (.region .acceptCount) rfl rfl

/-! ## `ReceiverPre * Escrow`, the composition `Channel.lean` has to write -/

/-- What a channel contract's `Escrow` looks like: this session holds a payload. -/
def escrowHolds (session : serverTopology.ChannelId ()) (payload : Nat) :
    NetworkAssertion fixtureAgreement where
  holds := fun world => world.escrow () session = some payload
  footprint := fun fragment => fragment = .escrow () session
  framed := by
    intro left right agrees
    have same : left.escrow () session = right.escrow () session := agrees _ rfl
    rw [same]

/-- And what its `ReceiverPre` looks like: the receiver is at a known position. -/
def receiverAt (session : serverTopology.ChannelId ()) (position : Nat) :
    NetworkAssertion fixtureAgreement where
  holds := fun world => world.received () session = position
  footprint := fun fragment => fragment = .session () session
  framed := by
    intro left right agrees
    have same : left.received () session = right.received () session := agrees _ rfl
    rw [same]

/--
**`ReceiverPre * Escrow` is formable on the same session.**

`docs/PROCESS.md` §3 requires `receive`'s precondition to be exactly this
conjunction. If `escrow` and `session` were one fragment — as an earlier
revision of `NetworkFragment` had them — these two would overlap, `Separate`
would be false, and `sep` could not be applied. This theorem is why the
constructor was split.
-/
theorem receiver_pre_separate_from_escrow
    (session : serverTopology.ChannelId ()) (payload position : Nat) :
    NetworkAssertion.Separate (receiverAt session position)
      (escrowHolds session payload) := by
  rintro fragment (rfl : fragment = _) (overlap : _ = _)
  simp at overlap

/-- So the conjunction exists, and means what it should. -/
theorem receive_precondition_holds (session : serverTopology.ChannelId ())
    (payload position : Nat) (world : FixtureWorld) :
    ((receiverAt session position).sep (escrowHolds session payload)
      (receiver_pre_separate_from_escrow session payload position)).holds world ↔
      (world.received () session = position ∧ world.escrow () session = some payload) :=
  Iff.rfl

/-! ## Framing at a concrete world -/

/--
Accepting a connection does not disturb the route table assertion.

`frame_of_disjoint_scope` in the shape `docs/PROCESS.md` §8 states it: a scope
disjoint from the assertion's footprint, and a step that changes nothing outside
that scope.
-/
theorem routeTable_survives_accept : routeTableEmpty.holds afterAccept :=
  routeTableEmpty.frame_of_disjoint_scope
    (scope := fun fragment => fragment = .region .acceptCount)
    (fun _ inScope overlap => by
      rw [inScope] at overlap
      injection overlap with regions
      exact absurd regions (by decide))
    (before := quiet)
    (fun fragment outside => by
      cases fragment with
      | region region =>
        cases region
        · rfl
        · exact absurd rfl outside
      | _ => rfl)
    rfl

/--
**The separating conjunction's other half survives a step confined to this one.**

`sep_right_survives_left_step` is the theorem `Separate` exists for, and this is
it at a concrete step: writing the accept count leaves the route table claim
standing, with no re-proof of the route table's own invariant.
-/
theorem routeTable_survives_a_step_in_the_accept_count :
    routeTableEmpty.holds afterAccept :=
  NetworkAssertion.sep_right_survives_left_step
    acceptedSomething routeTableEmpty
    (NetworkAssertion.separate_symm regions_are_separate)
    (before := quiet)
    (fun fragment outside => by
      cases fragment with
      | region region =>
        cases region
        · rfl
        · exact absurd rfl outside
      | _ => rfl)
    rfl

/-! ## The footprint is enforced

Everything above would still elaborate if `framed` were dropped and `footprint`
were a comment. This is the part that would not.
-/

/--
**No assertion with an empty footprint can read `acceptCount`.**

`framed` at an empty footprint says: any two worlds whatsoever have the same
truth value, because there is nothing to agree about. Two worlds differing only
in `acceptCount` then force a contradiction.

So the footprint is a genuine upper bound on what an assertion may depend on,
which is the property `frame` is sound by. If `framed` were weakened to hold
only at equal worlds this theorem would stop being provable and this file would
fail to build.

It would *not* fail if `framed` were weakened to a one-way implication, because
`agreesSymm` makes the two forms equivalent — that is
`NetworkAssertion.framed_backward`, stated in the library precisely because no
fixture could catch its removal. An earlier revision of this note claimed the
one-way weakening was caught here. It is not.
-/
theorem understated_footprint_impossible
    (assertion : NetworkAssertion fixtureAgreement)
    (claimsNothing : ∀ fragment, ¬ assertion.footprint fragment)
    (readsAcceptCount : assertion.holds = fun world => 0 < world.acceptCount) :
    False := by
  have same := assertion.framed quiet afterAccept
    (fun fragment member => absurd member (claimsNothing fragment))
  rw [readsAcceptCount] at same
  exact absurd (same.mpr Nat.zero_lt_one) (by decide)

/--
The same defect stated the way an author would hit it: `acceptedSomething` with
its footprint erased is not constructible.

`understated_footprint_impossible` is the general statement; this is the witness
that it bites on an assertion this file actually builds, so the general one is
not vacuous for want of a satisfiable instance.
-/
theorem acceptedSomething_needs_its_region
    (assertion : NetworkAssertion fixtureAgreement)
    (sameMeaning : assertion.holds = acceptedSomething.holds) :
    ∃ fragment, assertion.footprint fragment :=
  (Classical.em (∃ fragment, assertion.footprint fragment)).elim id
    (fun empty => (understated_footprint_impossible assertion
      (fun fragment member => empty ⟨fragment, member⟩) sameMeaning).elim)

/-! ## What `agreesGlue` does not say

`Grass/Process/Network/Assertion.lean`'s module note claimed `agreesGlue` is
"exactly the statement that the fragments name a *complete and independent
decomposition* of the world: agreement on a set of fragments carries no
information about the rest". Local adversarial review refuted it and this is the
refutation, kept because the claim is the natural reading of a gluing law and was
believed for several revisions. §10.137.
-/

/-- **The agreement that distinguishes nothing**, over a world of any shape.

`agreesGlue` constrains the agreement and not the world: this satisfies every
law, and it does so over `FixtureWorld` or over a world carrying a cross-fragment
invariant as a field, indifferently. An earlier note in
`Grass/Process/Network/Assertion.lean` said such a world could not satisfy the
law. §10.137. -/
def blindAgreement {World : Type} : WorldAgreement serverTopology World where
  Agrees _ _ _ := True
  agreesRefl := by intro _ _; trivial
  agreesSymm := by intro _ _ _ _; trivial
  agreesTrans := by intro _ _ _ _ _ _; trivial
  agreesGlue := by
    intro _ left _
    exact ⟨left, fun _ _ => trivial, fun _ _ => trivial⟩

open Classical in
/--
**An agreement that says nothing except at one fragment, where it says
everything.**

`agreesGlue` asks that any two worlds can be *mixed* along any set of fragments.
It does not ask that the fragments cover the world, and this satisfies it: when
`.obligations` is inside, the mixture is `left`, and every fragment outside is
not `.obligations` so its clause is vacuous; when it is outside, the mixture is
`right` symmetrically.

`WorldAgreement.subsingleton_of_forced_equality` is not violated, because it
refuses the agreement that forces equality at *every* fragment. This one forces
it at one.
-/
def leakyAgreement : WorldAgreement serverTopology FixtureWorld where
  Agrees fragment left right := fragment = .obligations → left = right
  agreesRefl := by intro _ _ _; rfl
  agreesSymm := by
    intro fragment left right holds isObligations
    exact (holds isObligations).symm
  agreesTrans := by
    intro fragment a b c first second isObligations
    exact (first isObligations).trans (second isObligations)
  agreesGlue := by
    intro inside left right
    by_cases obligationsInside : inside .obligations
    · refine ⟨left, ?_, ?_⟩
      · intro _ _ _; rfl
      · intro fragment outside isObligations
        exact absurd (isObligations ▸ obligationsInside) outside
    · refine ⟨right, ?_, ?_⟩
      · intro fragment isInside isObligations
        exact absurd (isObligations ▸ isInside) obligationsInside
      · intro _ _ _; rfl

/-- **So agreement at one fragment can determine every other**, and gluing does
not forbid it. An assertion framed by `{.obligations}` under this agreement may
depend on anything at all. -/
theorem gluing_does_not_bound_the_footprint (left right : FixtureWorld)
    (agreed : leakyAgreement.Agrees .obligations left right) : left = right :=
  agreed rfl

end Grass.Process.Tests.NetworkAssertions
