import Grass.Process.Network.Assertion
import Tests.Process.M2GraphFixtures

/-!
# What the footprint is, and what `agreesGlue` does not make it

`Grass/Process/Network/Assertion.lean` makes two claims that a module cannot
check about itself, because they are claims about what its types *reject*. This
fixture checks them.

* `framed` bounds what an assertion may read *under an agreement that separates
  enough*. `understated_footprint_impossible` is that under `fixtureAgreement`:
  no assertion with an empty footprint can read `acceptCount`. It is not general
  — `leaky_footprint_reads_outside_it` is the failure under `leakyAgreement`, and
  the deep note beside it says so.
* `agreesGlue` excludes the degenerate *equality* agreement, and more besides —
  `orderedComponentwise_is_not_equality` exhibits an agreement that is not
  equality and `orderedComponentwise_has_no_glue` is the law rejecting it, so
  "and no more than that", which an earlier version of this bullet said, is wrong
  in the other direction. `fixtureAgreement` discharges it,
  and `separate_fragments_are_independent` shows the payoff — two worlds agreeing
  on one fragment and differing on another, which the equality agreement could
  not exhibit. What the law does not do is make the footprint a bound in general:
  `gluing_does_not_bound_the_footprint` refutes that, `leakyLeak` is an assertion
  whose footprint is a label, and `blindAgreement` discharges the law while
  distinguishing nothing at all.

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
*demands* — `blindAgreement` below satisfies the law at a world of any shape at
all. §10.137. An earlier draft of this fixture had a single
`listenerCursor : Nat` read by every `instanceState` fragment, which made two
assertions about different slots `Separate` while reading the same field —
exactly the aliasing no agreement determining both slots can survive.
-/

namespace Grass.Process.Tests.NetworkAssertions

open Grass.Process
open Grass.Process.Tests

universe fixtureWorld

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
why this shape is what makes the `agreesGlue` discharge componentwise — not on
why it is forced, because it is not.
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
because *this* world is a product over the fragments — a fact about
`FixtureWorld` and not the point of the law, which asks only that some mixture
exist. §10.137.

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

So the footprint is a genuine upper bound on what an assertion may depend on
*under this agreement*, which is the property `frame` is sound by here. Not in
general: `leaky_footprint_reads_outside_it` builds the assertion that reads past
its footprint under `leakyAgreement`, and `frame` is stated over an arbitrary
agreement. If `framed` were weakened to hold
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
def blindAgreement {World : Type fixtureWorld} :
    WorldAgreement serverTopology World where
  Agrees _ _ _ := True
  agreesRefl := by intro _ _; trivial
  agreesSymm := by intro _ _ _ _; trivial
  agreesTrans := by intro _ _ _ _ _ _; trivial
  agreesGlue := by
    intro _ left _
    exact ⟨left, fun _ _ => trivial, fun _ _ => trivial⟩

/-- **A cross-fragment invariant, carried as a field.**

Two genuinely distinct components tied by an inequality — not an aliasing
witness. The earlier fixture here was a TangledWorld whose two components were
pinned *equal*, which made every determining agreement over it an instance of the
equality degeneracy `WorldAgreement.subsingleton_of_forced_equality` already
covered. §10.137 records the round that found it. This one
carries the same direction and is not that. §10.137. -/
structure OrderedWorld where
  /-- The lower component. -/
  low : Nat
  /-- The upper component. -/
  high : Nat
  /-- And the invariant tying them, which is the point of the fixture. -/
  le : low ≤ high

/-- **`blindAgreement` is a `WorldAgreement` over it.**

The easy half: `agreesGlue` asks that some mixture exist, and the blind agreement
always has one, so a world carrying a cross-fragment invariant as a field does
satisfy the law. An instantiation and not a consumer — `blindAgreement` is
polymorphic, so the elaborator checked this when it checked that. -/
def orderedAgreement : WorldAgreement serverTopology OrderedWorld := blindAgreement

/-- **No agreement that *determines* the two components at two fragments can
glue**, for every such agreement rather than for one hand-picked relation.

The hypotheses are the whole of it: whatever the agreement is, at `.obligations`
it pins `low` and at `.observations` it pins `high`. Gluing at `{.obligations}`
then needs a world whose `low` comes from one argument and whose `high` comes
from the other, and `le` forbids the pair that crosses.

Determining, not reading. `orderedSplitAgreement` below reads `low` at one
fragment and `high` at another and glues anyway, so "reads distinct components at
distinct fragments" is not the hypothesis and an earlier version of the prose in
`Grass/Process/Network/Assertion.lean` said it was. §10.137. -/
theorem ordered_no_glue_general
    (Agrees : NetworkFragment serverTopology → OrderedWorld → OrderedWorld → Prop)
    (determinesLow : ∀ a b, Agrees .obligations a b → a.low = b.low)
    (determinesHigh : ∀ a b, Agrees .observations a b → a.high = b.high) :
    ¬ (∀ (inside : NetworkFragment serverTopology → Prop) (left right : OrderedWorld),
        ∃ mixed, (∀ fragment, inside fragment → Agrees fragment mixed left) ∧
          (∀ fragment, ¬ inside fragment → Agrees fragment mixed right)) := by
  intro glue
  obtain ⟨mixed, inside, outside⟩ :=
    glue (fun fragment => fragment = .obligations) ⟨1, 1, Nat.le_refl 1⟩
      ⟨0, 0, Nat.le_refl 0⟩
  have fromLow : mixed.low = 1 := determinesLow _ _ (inside .obligations rfl)
  have fromHigh : mixed.high = 0 :=
    determinesHigh _ _ (outside .observations (by intro same; cases same))
  have bound := mixed.le
  omega

/-- The componentwise agreement over it: `.obligations` pins `low`,
`.observations` pins `high`, everything else says nothing. -/
def orderedComponentwise :
    NetworkFragment serverTopology → OrderedWorld → OrderedWorld → Prop
  | .obligations, a, b => a.low = b.low
  | .observations, a, b => a.high = b.high
  | _, _, _ => True

/-- **And it is an instance**, so the general theorem is not vacuous. -/
theorem orderedComponentwise_has_no_glue :
    ¬ (∀ (inside : NetworkFragment serverTopology → Prop) (left right : OrderedWorld),
        ∃ mixed, (∀ fragment, inside fragment → orderedComponentwise fragment mixed left) ∧
          (∀ fragment, ¬ inside fragment → orderedComponentwise fragment mixed right)) :=
  ordered_no_glue_general orderedComponentwise (fun _ _ agreed => agreed)
    (fun _ _ agreed => agreed)

/-- Reflexive. -/
theorem orderedComponentwise_refl (fragment : NetworkFragment serverTopology)
    (world : OrderedWorld) : orderedComponentwise fragment world world := by
  cases fragment <;> simp [orderedComponentwise]

/-- Symmetric. -/
theorem orderedComponentwise_symm (fragment : NetworkFragment serverTopology)
    (left right : OrderedWorld) (agreed : orderedComponentwise fragment left right) :
    orderedComponentwise fragment right left := by
  cases fragment <;> simp_all [orderedComponentwise]

/-- And transitive — so it is a candidate agreement in every respect but the
gluing law, which is what makes the next theorem say something. -/
theorem orderedComponentwise_trans (fragment : NetworkFragment serverTopology)
    (a b c : OrderedWorld) (first : orderedComponentwise fragment a b)
    (second : orderedComponentwise fragment b c) :
    orderedComponentwise fragment a c := by
  cases fragment <;> simp_all [orderedComponentwise]

/-- **So `agreesGlue` excludes more than the equality agreement.**

`orderedComponentwise` satisfies the other three laws — the three theorems above,
which an earlier version of this docstring asserted in prose in a file whose
subject is prose asserted without checking — it is *not* equality, since two
worlds differing in `high` agree at `.obligations`, and `agreesGlue` rejects it
all the same. An earlier version of this file's header said the law excludes the
equality agreement "and no more than that", which this refutes. §10.137. -/
theorem orderedComponentwise_is_not_equality :
    orderedComponentwise .obligations ⟨0, 5, by omega⟩ ⟨0, 7, by omega⟩ ∧
      (⟨0, 5, by omega⟩ : OrderedWorld) ≠ ⟨0, 7, by omega⟩ := by
  refine ⟨rfl, ?_⟩
  intro same
  have projected := congrArg OrderedWorld.high same
  simp at projected

/-- An agreement that *reads* `low` at one fragment and `high` at another
without determining either -- it sees `low`'s parity and `high`'s half.

`orderedSplit_does_not_determine_low` and `..._high` below are the witnesses;
this docstring asserted it in prose until a reviewer pointed out that the file's
whole subject is prose asserted without witnesses. -/
def orderedSplitAgrees :
    NetworkFragment serverTopology → OrderedWorld → OrderedWorld → Prop
  | .obligations, a, b => a.low % 2 = b.low % 2
  | .observations, a, b => a.high / 2 = b.high / 2
  | _, _, _ => True

open Classical in
/-- **And it glues.**

Which is why the word in the prose is *determines* and not *reads*. Gluing needs
a mixture that **agrees** with one argument inside the split and the other
outside; it does not need one that copies a component from each. A coarsening has
the slack to do that — here `2 * (right.high / 2) + left.low % 2` — and this
agreement reads distinct components at distinct fragments in the plainest sense.

The pair `orderedComponentwise` (pins, no glue) and this one (looks, glues) is
half the picture; `boundedAgreement` and `mirrorLooks` below are the other half,
and together they show neither property implies the other. §10.137. -/
def orderedSplitAgreement : WorldAgreement serverTopology OrderedWorld where
  Agrees := orderedSplitAgrees
  agreesRefl := by
    intro fragment world
    cases fragment <;> simp [orderedSplitAgrees]
  agreesSymm := by
    intro fragment left right agreed
    cases fragment <;> simp_all [orderedSplitAgrees]
  agreesTrans := by
    intro fragment a b c first second
    cases fragment <;> simp_all [orderedSplitAgrees]
  agreesGlue := by
    intro inside left right
    by_cases obligationsInside : inside .obligations <;>
      by_cases observationsInside : inside .observations
    · refine ⟨left, ?_, ?_⟩
      · intro f _
        cases f <;> simp [orderedSplitAgrees]
      · intro f isOutside
        cases f <;> simp [orderedSplitAgrees] <;>
          first
            | exact absurd obligationsInside isOutside
            | exact absurd observationsInside isOutside
    · refine ⟨⟨left.low % 2, 2 * (right.high / 2) + left.low % 2, by omega⟩, ?_, ?_⟩
      · intro f isInside
        cases f <;> simp [orderedSplitAgrees] <;>
          first
            | omega
            | exact absurd isInside observationsInside
      · intro f isOutside
        cases f <;> simp [orderedSplitAgrees] <;>
          first
            | omega
            | exact absurd obligationsInside isOutside
    · refine ⟨⟨right.low % 2, 2 * (left.high / 2) + right.low % 2, by omega⟩, ?_, ?_⟩
      · intro f isInside
        cases f <;> simp [orderedSplitAgrees] <;>
          first
            | omega
            | exact absurd isInside obligationsInside
      · intro f isOutside
        cases f <;> simp [orderedSplitAgrees] <;>
          first
            | omega
            | exact absurd observationsInside isOutside
    · refine ⟨right, ?_, ?_⟩
      · intro f isInside
        cases f <;> simp [orderedSplitAgrees] <;>
          first
            | exact absurd isInside obligationsInside
            | exact absurd isInside observationsInside
      · intro f _
        cases f <;> simp [orderedSplitAgrees]

/-! ## Four cases, and the theorem that explains two of them

Three rounds of local adversarial review each produced a class-level sentence of
the form "a world carrying a cross-fragment invariant has no agreement like
*that*", narrowing the predicate each time -- componentwise, separating,
determining -- and each was refuted by compiling a witness.

The axis those sentences named is the wrong one, and every world below carries a
cross-fragment invariant, so it is held *fixed* here rather than varied. What
varies is:

* the agreement's clauses **determine** the two components, or only **look** at
  them;
* the mixture `agreesGlue` asks for exists, or does not.

All four combinations are inhabited -- `orderedComponentwise`, `boundedAgreement`,
`mirrorLooks`, `orderedSplitAgreement` -- so neither property implies the other.

For the *determining* row that is not the end of it, and the section below --
"What determining agreements cost" -- has the theorem: an agreement determining
two components at two distinct fragments can glue only if those components are a
rectangle. So the first two cases are one criterion rather than an unexplained
pair, and the invariant an author writes matters only insofar as it takes the
world out of that shape. The converse is narrower than the necessary direction
and the section says where. §10.137. -/

/-- **Corner one: an invariant, a determining agreement, and no glue.**

`OrderedWorld`'s `low ≤ high` is not a product on the two components -- taking
`low` from one world and `high` from another can cross the bound -- so an
agreement pinning both cannot mix. This is `ordered_no_glue_general` above, and
for five rounds it was mistaken for the general case. -/
theorem corner_invariant_determining_no_glue :
    ¬ (∀ (inside : NetworkFragment serverTopology → Prop) (left right : OrderedWorld),
        ∃ mixed, (∀ fragment, inside fragment → orderedComponentwise fragment mixed left) ∧
          (∀ fragment, ¬ inside fragment → orderedComponentwise fragment mixed right)) :=
  orderedComponentwise_has_no_glue

/-- **Corner two: an invariant, a determining agreement, and glue anyway.**

`tie` is a genuine cross-fragment field. It is also *implied* by the two
per-component bounds, so every mixture satisfies it and the determining
agreement mixes freely. Carrying a cross-fragment invariant is therefore not
what costs a world its determining agreements, which four rounds of this
section's prose asserted. -/
structure BoundedTiedWorld where
  /-- Bounded above by three. -/
  low : Nat
  /-- Bounded below by four. -/
  high : Nat
  /-- Per-component, not cross-fragment. -/
  lowSmall : low ≤ 3
  /-- Likewise. -/
  highBig : 4 ≤ high
  /-- And the cross-fragment invariant, carried as a field. -/
  tie : low < high

/-- Pins `low` at `.obligations` and `high` at `.observations`. -/
def boundedComponentwise :
    NetworkFragment serverTopology → BoundedTiedWorld → BoundedTiedWorld → Prop
  | .obligations, a, b => a.low = b.low
  | .observations, a, b => a.high = b.high
  | _, _, _ => True

open Classical in
/-- **And it is a `WorldAgreement`**, so it glues. -/
def boundedAgreement : WorldAgreement serverTopology BoundedTiedWorld where
  Agrees := boundedComponentwise
  agreesRefl := by intro fragment _; cases fragment <;> simp [boundedComponentwise]
  agreesSymm := by
    intro fragment a b agreed
    cases fragment <;> simp_all [boundedComponentwise]
  agreesTrans := by
    intro fragment a b c first second
    cases fragment <;> simp_all [boundedComponentwise]
  agreesGlue := by
    intro inside left right
    refine ⟨⟨if inside .obligations then left.low else right.low,
             if inside .observations then left.high else right.high,
             by by_cases picked : inside .obligations <;>
                simp [picked] <;> first | exact left.lowSmall | exact right.lowSmall,
             by by_cases picked : inside .observations <;>
                simp [picked] <;> first | exact left.highBig | exact right.highBig,
             by
               have small : (if inside .obligations then left.low else right.low) ≤ 3 := by
                 by_cases picked : inside .obligations <;>
                   simp [picked] <;> first | exact left.lowSmall | exact right.lowSmall
               have big : 4 ≤ (if inside .observations then left.high else right.high) := by
                 by_cases picked : inside .observations <;>
                   simp [picked] <;> first | exact left.highBig | exact right.highBig
               omega⟩, ?_, ?_⟩
    · intro fragment isInside
      cases fragment <;> simp [boundedComponentwise, isInside]
    · intro fragment isOutside
      cases fragment <;> simp [boundedComponentwise, isOutside]

/-- It determines `low`. -/
theorem bounded_determines_low (left right : BoundedTiedWorld)
    (agreed : boundedAgreement.Agrees .obligations left right) : left.low = right.low :=
  agreed

/-- And `high`. So it satisfies `ordered_no_glue_general`'s hypothesis pair
exactly, over a world with a cross-fragment invariant, and glues. -/
theorem bounded_determines_high (left right : BoundedTiedWorld)
    (agreed : boundedAgreement.Agrees .observations left right) : left.high = right.high :=
  agreed

/-- And the world is not a subsingleton, so neither is the observation. -/
theorem bounded_is_not_trivial :
    (⟨0, 4, by omega, by omega, by omega⟩ : BoundedTiedWorld)
      ≠ ⟨3, 9, by omega, by omega, by omega⟩ := by
  intro same
  have projected := congrArg BoundedTiedWorld.low same
  simp at projected

/-! ## What determining agreements cost, stated as a theorem

Five rounds of local adversarial review produced five class-level sentences of
the form "a world like *this* has no agreement like *that*", and each was refuted
by compiling a witness. The sixth withdrew the claim and exhibited four cases
instead. The seventh found the theorem.

For an agreement that *determines* two components at two fragments, gluing
reduces exactly to a property of the world alone: the two determined components
must range over a **rectangle**, meaning every combination of one world's first
and another's second is realised by some world. That is the criterion the five
sentences were groping for, it is provable in both directions, and it settles the
four cases below as instances rather than leaving them as an unexplained
collection. §10.137. -/

/--
**A determining agreement that glues forces a rectangle.**

Gluing at `{.obligations}` produces a world agreeing with the first argument
there and the second at `.observations`; determining turns those agreements into
equations on the two components. So the pair `⟨lo a, hi b⟩` is realised for every
`a` and `b`, which is what a rectangle is.

Stated over arbitrary `lo` and `hi` rather than over a fixture, because the point
is that *nothing about the world* is assumed: whatever two projections an
agreement pins, gluing forces them independent. -/
theorem determining_glue_forces_rectangle
    {World : Type} (lo hi : World → Nat)
    (Agrees : NetworkFragment serverTopology → World → World → Prop)
    (determinesLo : ∀ a b, Agrees .obligations a b → lo a = lo b)
    (determinesHi : ∀ a b, Agrees .observations a b → hi a = hi b)
    (glue : ∀ (inside : NetworkFragment serverTopology → Prop) (left right : World),
        ∃ mixed, (∀ fragment, inside fragment → Agrees fragment mixed left) ∧
          (∀ fragment, ¬ inside fragment → Agrees fragment mixed right))
    (a b : World) : ∃ mixed : World, lo mixed = lo a ∧ hi mixed = hi b := by
  obtain ⟨mixed, inside, outside⟩ :=
    glue (fun fragment => fragment = .obligations) a b
  exact ⟨mixed, determinesLo _ _ (inside .obligations rfl),
    determinesHi _ _ (outside .observations (by intro same; cases same))⟩

open Classical in
/--
**And a rectangle gives one back**, for the exactly-componentwise agreement.

The converse, so the criterion is a criterion and not a one-way necessary
condition. Stated for the clause shape the fixtures use — each of the two
fragments reading its own component exactly, every other fragment saying
nothing — because that is the agreement a rectangle is enough for. -/
theorem rectangle_gives_glue
    {World : Type} (lo hi : World → Nat)
    (Agrees : NetworkFragment serverTopology → World → World → Prop)
    (loClause : ∀ a b, Agrees .obligations a b ↔ lo a = lo b)
    (hiClause : ∀ a b, Agrees .observations a b ↔ hi a = hi b)
    (elsewhere : ∀ fragment a b, fragment ≠ .obligations → fragment ≠ .observations →
      Agrees fragment a b)
    (rectangle : ∀ a b : World, ∃ mixed : World, lo mixed = lo a ∧ hi mixed = hi b) :
    ∀ (inside : NetworkFragment serverTopology → Prop) (left right : World),
      ∃ mixed, (∀ fragment, inside fragment → Agrees fragment mixed left) ∧
        (∀ fragment, ¬ inside fragment → Agrees fragment mixed right) := by
  intro inside left right
  obtain ⟨mixed, atLow, atHigh⟩ :=
    rectangle (if inside .obligations then left else right)
      (if inside .observations then left else right)
  refine ⟨mixed, ?_, ?_⟩
  · intro fragment isInside
    match fragment with
    | .obligations => exact (loClause _ _).2 (by simp [isInside] at atLow ⊢; exact atLow)
    | .observations => exact (hiClause _ _).2 (by simp [isInside] at atHigh ⊢; exact atHigh)
    | .instanceState _ _ => exact elsewhere _ _ _ (by simp) (by simp)
    | .region _ => exact elsewhere _ _ _ (by simp) (by simp)
    | .escrow _ _ => exact elsewhere _ _ _ (by simp) (by simp)
    | .session _ _ => exact elsewhere _ _ _ (by simp) (by simp)
    | .pending => exact elsewhere _ _ _ (by simp) (by simp)
    | .nominals => exact elsewhere _ _ _ (by simp) (by simp)
  · intro fragment isOutside
    match fragment with
    | .obligations => exact (loClause _ _).2 (by simp [isOutside] at atLow ⊢; exact atLow)
    | .observations => exact (hiClause _ _).2 (by simp [isOutside] at atHigh ⊢; exact atHigh)
    | .instanceState _ _ => exact elsewhere _ _ _ (by simp) (by simp)
    | .region _ => exact elsewhere _ _ _ (by simp) (by simp)
    | .escrow _ _ => exact elsewhere _ _ _ (by simp) (by simp)
    | .session _ _ => exact elsewhere _ _ _ (by simp) (by simp)
    | .pending => exact elsewhere _ _ _ (by simp) (by simp)
    | .nominals => exact elsewhere _ _ _ (by simp) (by simp)

/-- **`OrderedWorld` is not a rectangle**: `low` from a high world and `high`
from a low one cross the bound. So `ordered_no_glue_general` above is an instance
of `determining_glue_forces_rectangle` rather than a fact of its own. -/
theorem ordered_is_not_a_rectangle :
    ¬ (∀ a b : OrderedWorld, ∃ mixed : OrderedWorld,
        mixed.low = a.low ∧ mixed.high = b.high) := by
  intro rectangle
  obtain ⟨mixed, atLow, atHigh⟩ :=
    rectangle ⟨1, 1, Nat.le_refl 1⟩ ⟨0, 0, Nat.le_refl 0⟩
  simp only [] at atLow atHigh
  have bound := mixed.le
  rw [atLow, atHigh] at bound
  exact absurd bound (by omega)

/-- **`BoundedTiedWorld` is one**, and by `determining_glue_forces_rectangle` it
had to be for `boundedAgreement` to exist.

This is the sharper version of what that fixture shows, with the hypothesis an
earlier version of this docstring dropped. A world whose components are not a
rectangle admits no agreement determining them *at two distinct fragments* --
`orderedSingleFragment` below determines both at one and glues over
`OrderedWorld`, so the qualifier is not decoration. Within that hypothesis the
consequence holds: `tie : low < high` follows from the two per-component bounds,
so the pair is still a product, and a field that took it out of product shape
would leave this case empty. -/
theorem bounded_is_a_rectangle :
    ∀ a b : BoundedTiedWorld, ∃ mixed : BoundedTiedWorld,
      mixed.low = a.low ∧ mixed.high = b.high := by
  intro a b
  exact ⟨⟨a.low, b.high, a.lowSmall, b.highBig, by
    have small := a.lowSmall
    have big := b.highBig
    omega⟩, rfl, rfl⟩

/-- It reads `low`'s parity without determining `low`. -/
theorem orderedSplit_does_not_determine_low :
    orderedSplitAgrees .obligations ⟨0, 0, Nat.le_refl 0⟩ ⟨2, 2, Nat.le_refl 2⟩ ∧
      (⟨0, 0, Nat.le_refl 0⟩ : OrderedWorld).low
        ≠ (⟨2, 2, Nat.le_refl 2⟩ : OrderedWorld).low := by
  refine ⟨rfl, ?_⟩
  simp

/-- And `high`'s half without determining `high`. -/
theorem orderedSplit_does_not_determine_high :
    orderedSplitAgrees .observations ⟨0, 0, Nat.le_refl 0⟩ ⟨1, 1, Nat.le_refl 1⟩ ∧
      (⟨0, 0, Nat.le_refl 0⟩ : OrderedWorld).high
        ≠ (⟨1, 1, Nat.le_refl 1⟩ : OrderedWorld).high := by
  refine ⟨rfl, ?_⟩
  simp

/-- **Corner three: an invariant, an agreement that only looks, and no glue.**

Two components pinned equal — the shape `OrderedWorld`'s docstring above
rejects as a *determining* witness, readmitted deliberately here because this
agreement determines nothing, so the equality degeneracy that made it useless
there cannot arise. Read together with that docstring rather than against it.

An agreement reading nothing but their parities. It determines neither component -- `mirror_does_not_determine_low` --
and it still has no mixture, because the parities have to come from opposite
sides of the split and `tie` refuses that. So "a world keeps the agreements that
only look at its components" is false too, which is the other half of what the
round §10.137 records refuted. -/
structure MirrorWorld where
  /-- One component. -/
  low : Nat
  /-- The other. -/
  high : Nat
  /-- Pinned equal. -/
  tie : low = high

/-- Parities only, at two fragments. -/
def mirrorLooks :
    NetworkFragment serverTopology → MirrorWorld → MirrorWorld → Prop
  | .obligations, a, b => a.low % 2 = b.low % 2
  | .observations, a, b => a.high % 2 = b.high % 2
  | _, _, _ => True

/-- It reads `low` without determining it. -/
theorem mirror_does_not_determine_low :
    mirrorLooks .obligations ⟨0, 0, rfl⟩ ⟨2, 2, rfl⟩ ∧
      (⟨0, 0, rfl⟩ : MirrorWorld).low ≠ (⟨2, 2, rfl⟩ : MirrorWorld).low := by
  refine ⟨rfl, ?_⟩
  simp

/-- **And it has no glue all the same.** -/
theorem mirror_looks_but_has_no_glue :
    ¬ (∀ (inside : NetworkFragment serverTopology → Prop) (left right : MirrorWorld),
        ∃ mixed, (∀ fragment, inside fragment → mirrorLooks fragment mixed left) ∧
          (∀ fragment, ¬ inside fragment → mirrorLooks fragment mixed right)) := by
  intro glue
  obtain ⟨mixed, inside, outside⟩ :=
    glue (fun fragment => fragment = .obligations) ⟨0, 0, rfl⟩ ⟨1, 1, rfl⟩
  have fromLow : mixed.low % 2 = 0 := inside .obligations rfl
  have fromHigh : mixed.high % 2 = 1 :=
    outside .observations (by intro same; cases same)
  have tie := mixed.tie
  omega

/-- **And the same clause shape glues over `OrderedWorld`.**

Corner three and corner four differ in *two* things -- the world and the
agreement -- so neither could be blamed for the difference, and an earlier
version of corner four's docstring blamed the world anyway. This holds
`mirrorLooks`'s parity/parity shape fixed and changes only `low = high` to
`low ≤ high`, which restores glue. So the world is one of the two variables and
not the whole story: `mirrorHalf_glues` below holds the *world* fixed and changes
only the clauses, and restores glue too. §10.137. -/
def orderedParity :
    NetworkFragment serverTopology → OrderedWorld → OrderedWorld → Prop
  | .obligations, a, b => a.low % 2 = b.low % 2
  | .observations, a, b => a.high % 2 = b.high % 2
  | _, _, _ => True

open Classical in
/-- Parity at both fragments, over the world with the weaker tie. -/
theorem orderedParity_glues :
    ∀ (inside : NetworkFragment serverTopology → Prop) (left right : OrderedWorld),
      ∃ mixed, (∀ fragment, inside fragment → orderedParity fragment mixed left) ∧
        (∀ fragment, ¬ inside fragment → orderedParity fragment mixed right) := by
  intro inside left right
  refine ⟨⟨(if inside .obligations then left else right).low % 2,
           (if inside .observations then left else right).high % 2 + 2, by omega⟩, ?_, ?_⟩
  · intro fragment isInside
    cases fragment <;> simp_all [orderedParity] <;> omega
  · intro fragment isOutside
    cases fragment <;> simp_all [orderedParity] <;> omega

/-- Parity and half, over `MirrorWorld` -- the world corner four's earlier
docstring blamed. -/
def mirrorHalf :
    NetworkFragment serverTopology → MirrorWorld → MirrorWorld → Prop
  | .obligations, a, b => a.low % 2 = b.low % 2
  | .observations, a, b => a.high / 2 = b.high / 2
  | _, _, _ => True

open Classical in
/-- **And it glues too**, so neither the world nor the clauses is "the"
difference between corners three and four. -/
theorem mirrorHalf_glues :
    ∀ (inside : NetworkFragment serverTopology → Prop) (left right : MirrorWorld),
      ∃ mixed, (∀ fragment, inside fragment → mirrorHalf fragment mixed left) ∧
        (∀ fragment, ¬ inside fragment → mirrorHalf fragment mixed right) := by
  intro inside left right
  refine ⟨⟨2 * ((if inside .observations then left else right).high / 2)
             + (if inside .obligations then left else right).low % 2,
           2 * ((if inside .observations then left else right).high / 2)
             + (if inside .obligations then left else right).low % 2, rfl⟩, ?_, ?_⟩
  · intro fragment isInside
    cases fragment <;> simp_all [mirrorHalf] <;> omega
  · intro fragment isOutside
    cases fragment <;> simp_all [mirrorHalf] <;> omega

/-- **And `mirrorLooks` determines `high` no more than `low`.**

Corner three's docstring says it determines neither component, and only the
`low` half had a witness. -/
theorem mirror_does_not_determine_high :
    mirrorLooks .observations ⟨0, 0, rfl⟩ ⟨2, 2, rfl⟩ ∧
      (⟨0, 0, rfl⟩ : MirrorWorld).high ≠ (⟨2, 2, rfl⟩ : MirrorWorld).high := by
  refine ⟨rfl, ?_⟩
  simp

/-! ### What the two directions do not add up to

They are not a biconditional, and an earlier version of the prose above said they
were. The forward direction quantifies over *any* agreement determining two
components at two fragments. The converse quantifies over one clause shape: each
of those two fragments reading its own component exactly, and every other
fragment saying nothing. That `elsewhere` hypothesis is load-bearing, and the two
fixtures here are what a reviewer built to show it. §10.137. -/

/-- A relation over the full rectangle `Nat × Nat` whose two named fragments read
one component each -- and which pins both at a *third* fragment. -/
def rectAgrees : NetworkFragment serverTopology → Nat × Nat → Nat × Nat → Prop
  | .obligations, a, b => a.1 = b.1
  | .observations, a, b => a.2 = b.2
  | .pending, a, b => a.1 = b.1 ∧ a.2 = b.2
  | _, _, _ => True

/-- It determines the first component at `.obligations`. -/
theorem rectAgrees_determines_fst (a b : Nat × Nat)
    (agreed : rectAgrees .obligations a b) : a.1 = b.1 := agreed

/-- And the second at `.observations`. -/
theorem rectAgrees_determines_snd (a b : Nat × Nat)
    (agreed : rectAgrees .observations a b) : a.2 = b.2 := agreed

/-- `Nat × Nat` is a rectangle -- every pair of components is realised. -/
theorem prod_is_a_rectangle :
    ∀ a b : Nat × Nat, ∃ mixed : Nat × Nat, mixed.1 = a.1 ∧ mixed.2 = b.2 :=
  fun a b => ⟨(a.1, b.2), rfl, rfl⟩

/--
**And it does not glue.**

So a rectangle is not sufficient. Gluing at `{.obligations}` needs a world
agreeing with `left` there and with `right` at every other fragment, `.pending`
included -- and `.pending` pins both components to `right` while `.obligations`
pins the first to `left`.

This is why `rectangle_gives_glue` carries `elsewhere` and why the criterion is
one-directional in general. Worth knowing when reading it: `elsewhere` excludes
every agreement actually used in this project, `logicalWorldAgreement` included,
since those have content at all eight fragments. §10.137. -/
theorem rectangle_is_not_sufficient :
    ¬ (∀ (inside : NetworkFragment serverTopology → Prop) (left right : Nat × Nat),
        ∃ mixed, (∀ fragment, inside fragment → rectAgrees fragment mixed left) ∧
          (∀ fragment, ¬ inside fragment → rectAgrees fragment mixed right)) := by
  intro glue
  obtain ⟨mixed, inside, outside⟩ :=
    glue (fun fragment => fragment = .obligations) (1, 0) (0, 0)
  have fromLeft : mixed.1 = 1 := inside .obligations rfl
  have fromRight := outside .pending (by intro same; cases same)
  exact absurd (fromLeft.symm.trans fromRight.1) (by decide)

/--
**And determining at *one* fragment escapes the forward direction entirely.**

`determining_glue_forces_rectangle` needs the two components determined at two
*distinct* fragments; nothing stops an agreement pinning both at the same one.
This does, over `OrderedWorld`, which is not a rectangle -- and it glues, because
the mixture only ever has to copy one argument whole.

So "a world whose invariant constrains the pair admits no determining agreement"
is false as stated, and an earlier version of the prose above stated it. What is
true is the two-fragment form. §10.137. -/
def orderedSingleFragment : WorldAgreement serverTopology OrderedWorld where
  Agrees
    | .obligations, a, b => a.low = b.low ∧ a.high = b.high
    | _, _, _ => True
  agreesRefl := by intro fragment _; cases fragment <;> simp
  agreesSymm := by
    intro fragment left right agreed
    cases fragment <;> simp_all
  agreesTrans := by
    intro fragment a b c first second
    cases fragment <;> simp_all
  agreesGlue := by
    classical
    intro inside left right
    by_cases obligationsInside : inside .obligations
    · refine ⟨left, ?_, ?_⟩
      · intro fragment _; cases fragment <;> simp
      · intro fragment isOutside
        cases fragment <;> simp_all
    · refine ⟨right, ?_, ?_⟩
      · intro fragment isInside
        cases fragment <;> simp_all
      · intro fragment _; cases fragment <;> simp

/-- It determines both components, so it is not blind. -/
theorem orderedSingleFragment_determines (left right : OrderedWorld)
    (agreed : orderedSingleFragment.Agrees .obligations left right) :
    left.low = right.low ∧ left.high = right.high := agreed

/-- And it is not the blind agreement: two worlds disagree at `.obligations`. -/
theorem orderedSingleFragment_is_not_blind :
    ¬ orderedSingleFragment.Agrees .obligations ⟨0, 0, Nat.le_refl 0⟩
        ⟨1, 1, Nat.le_refl 1⟩ := by
  intro agreed
  exact absurd agreed.1 (by decide)

/-- **Corner four: an invariant, an agreement that only looks, and glue.**

`orderedSplitAgreement` above. The coarsening has enough slack to satisfy both
sides of any split, which is why it survives where `mirrorLooks` does not: the
difference is `low ≤ high` against `low = high`, a fact about the world and the
agreement together and about neither alone. -/
theorem corner_invariant_looking_glue :
    ∀ (inside : NetworkFragment serverTopology → Prop) (left right : OrderedWorld),
      ∃ mixed, (∀ fragment, inside fragment → orderedSplitAgreement.Agrees fragment mixed left) ∧
        (∀ fragment, ¬ inside fragment → orderedSplitAgreement.Agrees fragment mixed right) :=
  orderedSplitAgreement.agreesGlue

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
not forbid it. -/
theorem gluing_does_not_bound_the_footprint (left right : FixtureWorld)
    (agreed : leakyAgreement.Agrees .obligations left right) : left = right :=
  agreed rfl

/-- **And here is the assertion that reads outside its own footprint.**

`understated_footprint_impossible`'s mirror. It is framed by `{.obligations}` and
its truth depends on `region .acceptCount`, which that footprint does not name —
admissible because `leakyAgreement`'s clause at `.obligations` forces the whole
world equal, so `framed` is discharged without the assertion reading only what it
declared.

The docstring above used to assert this in prose. In a file whose subject is
claims that outran their code, that was the wrong place for it. §10.137. -/
def leakyLeak : NetworkAssertion leakyAgreement where
  holds world := 0 < world.acceptCount
  footprint fragment := fragment = .obligations
  framed := by
    intro left right agrees
    have same : left = right := agrees .obligations rfl rfl
    rw [same]

/-- **And it distinguishes two worlds that differ only outside its footprint.**

Not "two worlds its footprint cannot see apart", which an earlier version said
and which is false of the agreement in play: under `leakyAgreement` the clause at
`.obligations` forces the whole world equal, so that footprint does separate
`quiet` from `afterAccept`. That is exactly why the assertion is admissible. It
is `fixtureAgreement` under which `{.obligations}` cannot tell them apart, and
that is not the agreement `leakyLeak` is framed against. -/
theorem leaky_footprint_reads_outside_it :
    ¬ (leakyLeak.holds quiet ↔ leakyLeak.holds afterAccept) := by
  intro same
  exact absurd (same.mpr Nat.zero_lt_one) (Nat.lt_irrefl 0)

end Grass.Process.Tests.NetworkAssertions
