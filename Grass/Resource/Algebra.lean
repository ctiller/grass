import Grass.Resource.Axis

/-!
# The generic resource algebra

`docs/RESOURCES.md` §4: "Both tiers use the open resource algebra." This module
is that algebra. It is *intended* for a semantics layer that cannot state its
process type without it, and for a process layer that builds network holdings and
capacity credit on top — and neither exists. An earlier version of this sentence named
both as present-tense importers; review checked and found the only importer is
`Tests/Resource/CompositionSplit.lean`. `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2
records the consequence: `compatible` is the *partial* in partial commutative and the
reason every law here is conditioned, and its only nontrivial instance is consumed by
nothing, so no proof in this tree has discharged a nontrivial compatibility side
condition.

**The full extent, since a later review measured it and the paragraph above concedes
only the importer question.** Of the twenty laws `OrderedPartialCommutativeResourceLaws`
declares, three are ever projected — `combineCancel`, `alternativeIdem` and
`alternativeLeCombine` — and all three uses are inside that one fixture; the other
seventeen are discharged by `Counting.laws` and `Exclusive.laws` and read by nothing.
`ResourceModel`, `HasResourceAxis`, `HasResourceLimit` and `ResourceLimit` have no
values or instances anywhere under `Grass/` or `Tests/`. `Counting.algebra` is built
and used by nothing, and `Exclusive` — the namespace that exists to show `compatible`
is not a hedge — is used by nothing either.

So this is a facility whose only safety property is that nothing calls it, which is
the defect class this branch has spent eleven rounds finding elsewhere in the layer.
It is kept rather than deleted because M7 and M9 are the stated consumers and
rewriting a twenty-law bundle later is worse than carrying it; what is not acceptable
is carrying it while a reader assumes it is load-bearing. Two audit blind spots hide
the extent from the gates: `ResourceAlgebra.compatible` is invisible to
`Tools/ConsultedAudit.py` because `StepPolicy.compatible` satisfies the same name,
and every lifecycle and exhaustion constructor is on `Tools/ReachabilityAudit.py`'s
allowlist as declared-ahead-of-its-milestone.

## Reconciling two sketches

The corpus displays this idea twice with different shapes.
`docs/SEMANTICS.md` shows `OrderedPartialCommutativeResourceLaws combine le`;
`docs/PROCESS.md` shows `OrderedCommutativeResourceAlgebra (Value axis)
(combine axis) (zero axis) (le axis)`, with a zero and a different name. They are
sketches of one thing, and this module unifies them rather than shipping both.

## Two compositions, not one

The bundle carries **two** binary operations, and conflating them is the error
this design exists to prevent.

`combine` is **parallel** or spatial composition: two subsystems holding
resources at the same time. Two sockets held simultaneously are two sockets, so
`combine` is cancellative and not idempotent.

`alternative` is **temporal** aggregation: peak demand across mutually exclusive
branches or serial phases. Two branches each needing one socket, only one of
which runs, peak at one socket -- so `alternative` is idempotent and is *not*
cancellative.

An earlier version had only `combine`, and cancellation was added to stop `max`
being a lawful resource algebra. That was a real defect -- `max` as a *parallel*
composition undercounts simultaneously held sockets -- but the fix alone made
`max` unavailable for the case where it is the correct operator, which would have
forced ordinary peak-bound proofs to be artificially additive. Both operations
are present, with the laws that distinguish them, and `alternativeLeCombine`
relates them.

`ResourceLifecyclePolicy.phaseExclusive` is the axis-level declaration that
holdings aggregate the second way.

The bundle also carries two values beyond the operations:

- **`zero`** appears in `docs/PROCESS.md`'s `ResourceMetric` as `empty : forall
  axis, valuation axis EmptyNetworkResourceState = zero axis`. Without an
  identity there is no such thing as an empty holding, and a subsystem holding
  nothing could not be composed with one that does.
- **`compatible`** is the "partial" in *partial* commutative. This is the Iris
  sense — validity, not undefinedness. Two holdings that cannot lawfully coexist
  are incompatible, and the algebra's laws are conditioned on compatibility so
  that combining them proves nothing rather than proving something false. An
  exclusive holding of the same unique resource, held twice, is the case this
  exists for.

## Why the laws are conditioned

`combineAssoc` and friends hold only for compatible operands. A total,
unconditioned algebra would let a proof combine two exclusive claims to the same
socket and derive a bound from the result. `docs/FOUNDATION.md` law 20 names that
failure directly: affine transfers must not be double counted.
-/

namespace Grass.Resource

universe u

/--
The laws an ordered partial commutative resource algebra satisfies.

`compatible` says which pairs may lawfully coexist; every law about `combine` is
conditioned on it. `le` is the substate order: `le a b` means `b` holds at least
what `a` does.
-/
structure OrderedPartialCommutativeResourceLaws {Value : Type u}
    (compatible : Value → Value → Prop)
    (combine : Value → Value → Value)
    (alternative : Value → Value → Value)
    (zero : Value)
    (le : Value → Value → Prop) : Prop where
  /-- Compatibility does not depend on the order of its operands. -/
  compatibleComm : ∀ a b, compatible a b → compatible b a
  /-- Nothing is incompatible with holding nothing. -/
  compatibleZero : ∀ a, compatible a zero
  /-- Combining compatible holdings does not depend on their order. -/
  combineComm : ∀ a b, compatible a b → combine a b = combine b a
  /-- Combining is associative where every pairing is compatible. -/
  combineAssoc : ∀ a b c,
    compatible a b → compatible (combine a b) c → compatible b c →
    compatible a (combine b c) →
    combine (combine a b) c = combine a (combine b c)
  /-- Holding nothing changes nothing. -/
  combineZero : ∀ a, combine a zero = a
  /-- The order is reflexive. -/
  leRefl : ∀ a, le a a
  /-- The order is transitive. -/
  leTrans : ∀ a b c, le a b → le b c → le a c
  /-- The order is antisymmetric, so a holding is determined by what it contains. -/
  leAntisymm : ∀ a b, le a b → le b a → a = b
  /-- Holding nothing is the least holding. -/
  zeroLe : ∀ a, le zero a
  /-- Adding a compatible holding never loses what was already held. This is
  what makes a bound on a composite bound each part. -/
  leCombine : ∀ a b, compatible a b → le a (combine a b)
  /-- Combining is monotone in each argument, where the results are defined. -/
  combineMonotone : ∀ a b c,
    le a b → compatible a c → compatible b c → le (combine a c) (combine b c)
  /-- Combining is cancellative: what a composite holds determines each part.

  This is `docs/PROCESS.md`'s `cancellation : LeftCancellationLaw`, and without
  it the laws above admit `max`. A `max` algebra satisfies commutativity,
  associativity, identity, monotonicity, and the order laws, and reports that one
  socket combined with one socket is one socket. That is the double count
  `docs/FOUNDATION.md` law 20 forbids, running in the direction that
  *under*-counts. -/
  combineCancel : ∀ a b c,
    compatible a c → compatible b c → combine a c = combine b c → a = b
  /-- A composite strictly exceeds a part unless the other part is empty. Stated
  as the contrapositive of absorption, this is what makes an additive reading
  mandatory rather than merely permitted. -/
  combineEqLeft : ∀ a b, compatible a b → combine a b = a → b = zero
  /-- Aggregating alternatives does not depend on their order. -/
  alternativeComm : ∀ a b, alternative a b = alternative b a
  /-- Aggregating alternatives is associative. -/
  alternativeAssoc : ∀ a b c,
    alternative (alternative a b) c = alternative a (alternative b c)
  /-- An alternative holding nothing changes nothing. -/
  alternativeZero : ∀ a, alternative a zero = a
  /-- **Idempotent.** Two branches with the same demand peak at that demand, not
  at twice it. This is precisely the law `combine` must not have, and the two
  together are what separate the operations. -/
  alternativeIdem : ∀ a, alternative a a = a
  /-- The peak covers each branch. -/
  leAlternative : ∀ a b, le a (alternative a b)
  /-- Aggregating alternatives is monotone. -/
  alternativeMonotone : ∀ a b c, le a b → le (alternative a c) (alternative b c)
  /-- The peak of two alternatives never exceeds what running both at once costs.
  This ties the operations together: an alternative bound is always a sound
  relaxation of a parallel one, never the reverse. -/
  alternativeLeCombine : ∀ a b, compatible a b → le (alternative a b) (combine a b)

/--
A resource algebra on `R`.

`R` is the resource parameter itself — a budget, an envelope, or a holding — and
this is how two of them compose. `docs/RESOURCES.md` §4: "A composed
specification combines semantic demands axis by axis. A composed plan combines
physical provisions, holdings, and flux proofs."
-/
structure ResourceAlgebra (R : Type u) where
  /-- Which pairs of resource values may lawfully coexist. -/
  compatible : R → R → Prop
  /-- How two compatible resource values compose. -/
  combine : R → R → R
  /-- How two mutually exclusive demands aggregate. -/
  alternative : R → R → R
  /-- The resource value holding nothing. -/
  zero : R
  /-- The substate order. -/
  le : R → R → Prop
  /-- The algebra's laws. -/
  laws : OrderedPartialCommutativeResourceLaws compatible combine alternative zero le

/--
Marks `R` as a resource model, fixing how its values compose.

`docs/SEMANTICS.md` makes this the class every resource-parameterized
specification is stated against.
-/
class ResourceModel (R : Type u) where
  /-- The algebra on `R`. -/
  algebra : ResourceAlgebra R

/--
Declares that resources of type `R` measure `axis`, and fixes the algebra of that
axis's values.

The axis's value algebra is separate from `R`'s own because they are different
things: `R` composes whole resource parameters, while an axis composes the
quantities on one dimension. A specification bounded on `residentBytes` says
nothing about `sockets`, which is what makes the framed realization theorem of
`docs/RESOURCES.md` §4 possible.
-/
class HasResourceAxis (R : Type u) [ResourceModel R] (axis : ResourceAxisName) where
  /-- The type of quantities on this axis. -/
  Value : Type
  /-- Which quantities may lawfully coexist. -/
  compatible : Value → Value → Prop
  /-- How two compatible quantities compose. -/
  combine : Value → Value → Value
  /-- How two mutually exclusive demands aggregate. -/
  alternative : Value → Value → Value
  /-- The quantity holding nothing. -/
  zero : Value
  /-- The order in which a bound is stated. -/
  le : Value → Value → Prop
  /-- The axis's laws. -/
  laws : OrderedPartialCommutativeResourceLaws compatible combine alternative zero le

/--
Declares that resources of type `R` export a bound on `axis`, together with what
happens at the bound and how holdings compose.

`docs/RESOURCES.md` §1 requires a semantic budget to carry exhaustion outcomes
visible at the product boundary; that is `exhaustion`. `lifecycle` carries the
composition law that stops double counting.
-/
class HasResourceLimit (R : Type u) [ResourceModel R] (axis : ResourceAxisName)
    extends HasResourceAxis R axis where
  /-- The bound this resource value exports on the axis. -/
  limit : R → Value
  /-- What the product does when the bound is reached. -/
  exhaustion : R → ResourceExhaustionPolicy axis
  /-- How holdings on this axis compose. -/
  lifecycle : R → ResourceLifecyclePolicy axis

/--
One axis's limit, as a structure rather than a class instance.

**Why this exists.** `docs/SEMANTICS.md` sketches a multi-axis specification as
`class WebServerResources (R) extends HasResourceLimit R .residentBytes,
HasResourceLimit R .connections, ...`. That does not elaborate: Lean deduplicates
parent structures by head constant, not by full type, so every axis after the
first is silently dropped with a `Duplicate parent structure` warning — and under
this repository's `warningAsError` it is a hard error. The sketch in the corpus
is not implementable as written.

A multi-axis specification therefore holds `ResourceLimit R axis` values as
*fields*:

```lean
class WebServerResources (R : Type) [ResourceModel R] where
  residentBytes : ResourceLimit R .residentBytes
  connections : ResourceLimit R .connections
  fixedAfterReady : R → Prop
```

`HasResourceLimit` remains for the single-axis case, where instance resolution is
the convenient thing.
-/
structure ResourceLimit (R : Type u) (axis : ResourceAxisName) where
  /-- The type of quantities on this axis. -/
  Value : Type
  /-- Which quantities may lawfully coexist. -/
  compatible : Value → Value → Prop
  /-- How two compatible quantities compose. -/
  combine : Value → Value → Value
  /-- How two mutually exclusive demands aggregate. -/
  alternative : Value → Value → Value
  /-- The quantity holding nothing. -/
  zero : Value
  /-- The order in which the bound is stated. -/
  le : Value → Value → Prop
  /-- The axis's laws. -/
  laws : OrderedPartialCommutativeResourceLaws compatible combine alternative zero le
  /-- The bound this resource value exports. -/
  limit : R → Value
  /-- What the product does when the bound is reached. -/
  exhaustion : R → ResourceExhaustionPolicy axis
  /-- How holdings on this axis compose. -/
  lifecycle : R → ResourceLifecyclePolicy axis

/-!
## The counting algebra

Most axes count things: sockets, handles, threads, streams, bytes. This section
proves the laws are satisfiable at all, which matters because an uninhabited law
bundle would make every theorem quantified over it vacuous.
-/

namespace Counting

/-- Counted quantities always coexist. Exclusivity is a property of what is being
counted, not of counting, and an axis that needs it supplies its own
compatibility. -/
def compatible (_a _b : Nat) : Prop := True

/-- Counted quantities held at once add. -/
def combine (a b : Nat) : Nat := a + b

/-- Counted quantities across exclusive branches peak. -/
def alternative (a b : Nat) : Nat := max a b

/-- The counting algebra's laws hold. -/
theorem laws : OrderedPartialCommutativeResourceLaws compatible combine alternative 0 (· ≤ ·) where
  compatibleComm := fun _ _ _ => trivial
  compatibleZero := fun _ => trivial
  combineComm := fun a b _ => Nat.add_comm a b
  combineAssoc := fun a b c _ _ _ _ => Nat.add_assoc a b c
  combineZero := fun a => Nat.add_zero a
  leRefl := fun a => Nat.le_refl a
  leTrans := fun _ _ _ hab hbc => Nat.le_trans hab hbc
  leAntisymm := fun _ _ hab hba => Nat.le_antisymm hab hba
  zeroLe := fun a => Nat.zero_le a
  leCombine := fun a b _ => Nat.le_add_right a b
  combineMonotone := fun _ _ c hab _ _ => Nat.add_le_add_right hab c
  combineCancel := fun _ _ _ _ _ h => Nat.add_right_cancel h
  combineEqLeft := fun a b _ h => by simp only [combine] at h; omega
  alternativeComm := fun a b => Nat.max_comm a b
  alternativeAssoc := fun a b c => Nat.max_assoc a b c
  alternativeZero := fun a => Nat.max_zero a
  alternativeIdem := fun a => Nat.max_self a
  leAlternative := fun a b => Nat.le_max_left a b
  alternativeMonotone := fun a b c _ => by simp only [alternative]; omega
  alternativeLeCombine := fun a b _ => by simp only [alternative, combine]; omega

/-- The counting algebra as a `ResourceAlgebra`, usable as the model for a
resource parameter that is a single count. -/
def algebra : ResourceAlgebra Nat where
  compatible := compatible
  combine := combine
  alternative := alternative
  zero := 0
  le := (· ≤ ·)
  laws := laws

end Counting

/-!
## The exclusive algebra

An exclusive quantity has at most one holder, so two nonzero holdings never
coexist.

This is the case `compatible` exists for, and it is proved here to show the
conditioned laws are usable and not merely a hedge. A unique socket, a lock, or
an exclusive loan composes this way, and the incompatibility is what stops a
proof from combining two claims to the same one.
-/

namespace Exclusive

/-- Two exclusive holdings coexist only if at most one of them is nonzero;
`not_compatible_of_both_held` is the consequence that matters. -/
def compatible (a b : Nat) : Prop := a = 0 ∨ b = 0

/-- Combining exclusive holdings adds them, which is only meaningful where they
are compatible. -/
def combine (a b : Nat) : Nat := a + b

/-- Exclusive branches peak rather than adding. -/
def alternative (a b : Nat) : Nat := max a b

/-- The exclusive algebra's laws hold. -/
theorem laws : OrderedPartialCommutativeResourceLaws compatible combine alternative 0 (· ≤ ·) where
  compatibleComm := fun _ _ h => h.symm
  compatibleZero := fun _ => .inr rfl
  combineComm := fun a b _ => Nat.add_comm a b
  combineAssoc := fun a b c _ _ _ _ => Nat.add_assoc a b c
  combineZero := fun a => Nat.add_zero a
  leRefl := fun a => Nat.le_refl a
  leTrans := fun _ _ _ hab hbc => Nat.le_trans hab hbc
  leAntisymm := fun _ _ hab hba => Nat.le_antisymm hab hba
  zeroLe := fun a => Nat.zero_le a
  leCombine := fun a b _ => Nat.le_add_right a b
  combineMonotone := fun _ _ c hab _ _ => Nat.add_le_add_right hab c
  combineCancel := fun _ _ _ _ _ h => Nat.add_right_cancel h
  combineEqLeft := fun a b _ h => by simp only [combine] at h; omega
  alternativeComm := fun a b => Nat.max_comm a b
  alternativeAssoc := fun a b c => Nat.max_assoc a b c
  alternativeZero := fun a => Nat.max_zero a
  alternativeIdem := fun a => Nat.max_self a
  leAlternative := fun a b => Nat.le_max_left a b
  alternativeMonotone := fun a b c _ => by simp only [alternative]; omega
  alternativeLeCombine := fun a b _ => by simp only [alternative, combine]; omega

/-- Two held exclusive resources are incompatible. This is the fact a
double-counting demand would fail against, and an earlier version of this line named
a specific corpus obligation as though that obligation consumed it. None does — this
namespace has no consumer at all, which `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2
records. -/
theorem not_compatible_of_both_held {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ compatible a b := by
  rintro (h | h)
  · exact ha h
  · exact hb h

end Exclusive

end Grass.Resource
