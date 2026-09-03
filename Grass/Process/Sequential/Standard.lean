import Grass.Process.Sequential.Adapter

/-!
# Selecting a standard realizer, and why the selection is forced

`docs/PROCESS.md` §4 lets a specification constructor register a canonical
sequential realizer, so that an application's "complete process-authoring
surface is one expression":

```lean
def processRealization : ProcessRealization spec :=
  ProcessRealization.standard (Grass.Std.Realizers.lookupExact spec)
```

That is only worth anything if the lookup is *forced*. If two lookups of one
specification could select different realizers, the one expression would be
choosing a program rather than naming one, and §4's "the final certificate
cannot silently use a different graph" would be false at the selection rather
than at the elaboration.

`selection_is_determined` is that theorem, and everything else here exists to
make it provable.

## What is abstract, and why

§4's declarations mention `SpecProcess`, `ResourceModel`, `StandardRealizerKey`
and `DefinitionalOrCanonicalSpecEquality`, none of which exists in this tree —
the first two are the specification and memory layers', and the last two are
undeclared anywhere. So the registry here is parameterised by the specification
type, the key type, the realization type, and the equality relation.

That is not a weakening. The theorem is about the *shape* of the registry laws
and holds whatever those four are, which is what makes it worth stating before
they exist: if the shape were wrong, filling in the types would not fix it.

## The finding this module produced

§4's registry carries `unique`, and its `ExactStandardRealizerLookup` carries a
second `unique` of its own. **The second is derivable from the first**, but only
if the spec equality is transitive and symmetric —
`lookupUniquenessIsRedundant` is the derivation and it uses exactly those two
laws.

That matters because `DefinitionalOrCanonicalSpecEquality` is named for a
disjunction — "definitional *or* canonical" — and a disjunction of two
equivalences need not be transitive. If it is not, the two fields are
independent and §4 is right to state both; if it is, one of them is noise.
`docs/PROCESS_IMPLEMENTATION_PLAN.md` §10.40 records the question.
-/

namespace Grass.Process

universe u

/-! ## Spec equality -/

/--
§4's `DefinitionalOrCanonicalSpecEquality`, as the relation the registry laws
need it to be.

An equivalence, and each law is used below: `symm` and `trans` by
`lookupUniquenessIsRedundant`, `refl` by `lookup_of_own_entry`. Supplying it as
a structure rather than assuming `Eq` is what makes the abstraction honest —
"definitional or canonical" is explicitly not syntactic equality.
-/
structure SpecEquivalence (Spec : Type u) : Type u where
  /-- When two specifications are the same specification. -/
  Equal : Spec → Spec → Prop
  /-- Every specification is itself. -/
  refl : ∀ spec, Equal spec spec
  /-- The relation does not depend on which side you look from. -/
  symm : ∀ left right, Equal left right → Equal right left
  /--
  And it composes.

  The law `lookupUniquenessIsRedundant` turns on, and the one a "definitional or
  canonical" disjunction is least likely to have.
  -/
  trans : ∀ left middle right, Equal left middle → Equal middle right → Equal left right

/-! ## The registry -/

/-- One registered realizer: a specification, a key, and the realization. -/
structure StandardRealizerEntry (Spec Key Realization : Type u) : Type u where
  /-- The specification this entry realizes. -/
  spec : Spec
  /-- Its key. -/
  key : Key
  /-- And the realization itself. -/
  realization : Realization

/--
§4's `StandardRealizerRegistry`.

Two laws where §4 states one, and the second is the one that makes a key worth
having: without `keysDistinct`, `unique` says two entries for one specification
share a key while leaving them free to be different entries, so a lookup could
still select two different realizations and satisfy every field.
-/
structure StandardRealizerRegistry (Spec Key Realization : Type u)
    (equivalence : SpecEquivalence Spec) : Type u where
  /-- What is registered. -/
  entries : List (StandardRealizerEntry Spec Key Realization)
  /-- §4's law: one specification, one key. -/
  unique : ∀ left ∈ entries, ∀ right ∈ entries,
    equivalence.Equal left.spec right.spec → left.key = right.key
  /--
  **And one key, one entry.**

  Not in §4's declaration, and without it the registry law is about names rather
  than about programs: two entries could share a key, agree on their
  specification, and carry different realizations.
  -/
  keysDistinct : ∀ left ∈ entries, ∀ right ∈ entries, left.key = right.key → left = right

/-! ## Looking one up -/

/--
§4's `ExactStandardRealizerLookup`.

`unique` is §4's field and is derivable — see `lookupUniquenessIsRedundant` and
the module note. It is kept because §4 states it and because the derivation
depends on the spec equality being transitive, which is exactly what a
"definitional or canonical" relation might not be.
-/
structure ExactStandardRealizerLookup {Spec Key Realization : Type u}
    {equivalence : SpecEquivalence Spec}
    (registry : StandardRealizerRegistry Spec Key Realization equivalence)
    (spec : Spec) : Type u where
  /-- The entry selected. -/
  entry : StandardRealizerEntry Spec Key Realization
  /-- It is registered. -/
  member : entry ∈ registry.entries
  /-- And it realizes this specification. -/
  exactSpec : equivalence.Equal entry.spec spec
  /-- And every other entry that would match selects the same key. -/
  unique : ∀ other ∈ registry.entries,
    equivalence.Equal other.spec spec → other.key = entry.key

namespace ExactStandardRealizerLookup

variable {Spec Key Realization : Type u} {equivalence : SpecEquivalence Spec}
  {registry : StandardRealizerRegistry Spec Key Realization equivalence} {spec : Spec}

/--
**§4's lookup uniqueness is derivable from its registry uniqueness.**

Given `other.spec ≈ spec` and `entry.spec ≈ spec`, symmetry and transitivity
give `other.spec ≈ entry.spec`, and the registry law does the rest.

Both equivalence laws are load-bearing, which is the point of stating this: a
"definitional or canonical" equality is a disjunction of two relations, and a
disjunction of two equivalences need not be transitive. If it is not, §4 is
right to state both fields and this theorem does not apply; if it is, one of
them is noise. §10.40 records the question rather than answering it.
-/
theorem lookupUniquenessIsRedundant
    (entry : StandardRealizerEntry Spec Key Realization)
    (member : entry ∈ registry.entries) (exactSpec : equivalence.Equal entry.spec spec)
    (other : StandardRealizerEntry Spec Key Realization) (otherMember : other ∈ registry.entries)
    (otherMatches : equivalence.Equal other.spec spec) : other.key = entry.key :=
  registry.unique other otherMember entry member
    (equivalence.trans other.spec spec entry.spec otherMatches
      (equivalence.symm entry.spec spec exactSpec))

/--
**Two lookups of one specification select the same entry.**

The theorem the whole module is for. §4's application-side promise is that
selecting a registered standard realizer "must require one expression at the
application process boundary" — and an expression that could denote two
different programs is not a selection.

Both registry laws are used: `unique` to force the keys together and
`keysDistinct` to force the entries together. With only §4's stated `unique`
this would conclude that the two selections share a *name*.
-/
theorem selection_is_determined (left right : ExactStandardRealizerLookup registry spec) :
    left.entry = right.entry := by
  have sameKey : left.entry.key = right.entry.key :=
    right.unique left.entry left.member left.exactSpec
  exact registry.keysDistinct left.entry left.member right.entry right.member sameKey

/--
**So the realization is determined too.**

§4's "the final certificate cannot silently use a different graph", at the
selection rather than at the elaboration: two applications naming the same
specification get the same program, not merely the same key.
-/
theorem realization_is_determined (left right : ExactStandardRealizerLookup registry spec) :
    left.entry.realization = right.entry.realization :=
  congrArg StandardRealizerEntry.realization (selection_is_determined left right)

/-- And the same specification, which is what the lookup was asked for. -/
theorem spec_is_determined (left right : ExactStandardRealizerLookup registry spec) :
    left.entry.spec = right.entry.spec :=
  congrArg StandardRealizerEntry.spec (selection_is_determined left right)

end ExactStandardRealizerLookup

/--
**A registered entry looks itself up.**

The inhabitance check, and the one place `SpecEquivalence.refl` is used. Without
it every theorem above is about an empty class: a registry could satisfy both
laws with no entry ever matching anything.
-/
def lookup_of_own_entry {Spec Key Realization : Type u} {equivalence : SpecEquivalence Spec}
    (registry : StandardRealizerRegistry Spec Key Realization equivalence)
    (entry : StandardRealizerEntry Spec Key Realization) (member : entry ∈ registry.entries) :
    ExactStandardRealizerLookup registry entry.spec where
  entry := entry
  member := member
  exactSpec := equivalence.refl entry.spec
  unique := fun other otherMember matches' =>
    registry.unique other otherMember entry member matches'

end Grass.Process
