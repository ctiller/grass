import Grass.Process.Sequential.Standard

/-!
# A standard realizer registry, and what §4's stated law does not buy

`Grass/Process/Sequential/Standard.lean` proves that two lookups of one
specification select the same entry, and needs two registry laws to do it —
where `docs/PROCESS.md` §4 states one. This file is why the second is not
bookkeeping.

* `stdlib` is a small registry, and `selecting_gzip_is_forced` reads the
  determinacy back off it.
* `section_four_uniqueness_alone_permits_two_realizations` is the teeth: a list
  of entries satisfying §4's `unique` in full, carrying two *different*
  realizations for one specification. Under that list a lookup would be a
  choice, and §4's "one expression at the application process boundary" would be
  an expression that denotes two programs.
-/

namespace Grass.Process.Tests.Standard

open Grass.Process

/-! ## A registry -/

/-- Specifications, keys and realizations stand in for the real ones. -/
abbrev SpecName : Type := Nat

/-- Spec equality is ordinary equality here, which is the easy case. -/
def plainEquality : SpecEquivalence SpecName where
  Equal := Eq
  refl := fun _ => rfl
  symm := fun _ _ => Eq.symm
  trans := fun _ _ _ => Eq.trans

/-- The gzip filter's entry. -/
def gzipEntry : StandardRealizerEntry SpecName Nat String := ⟨0, 0, "gzip"⟩

/-- And a sort's. -/
def sortEntry : StandardRealizerEntry SpecName Nat String := ⟨1, 1, "sort"⟩

/-- A two-entry standard library. -/
def stdlib : StandardRealizerRegistry SpecName Nat String plainEquality where
  entries := [gzipEntry, sortEntry]
  unique := by
    rintro left leftMember right rightMember sameSpec
    simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember rightMember
    rcases leftMember with rfl | rfl
    · rcases rightMember with rfl | rfl
      · rfl
      · have differ : (0 : SpecName) = 1 := sameSpec
        exact absurd differ (by decide)
    · rcases rightMember with rfl | rfl
      · have differ : (1 : SpecName) = 0 := sameSpec
        exact absurd differ (by decide)
      · rfl
  keysDistinct := by
    rintro left leftMember right rightMember sameKey
    simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember rightMember
    rcases leftMember with rfl | rfl
    · rcases rightMember with rfl | rfl
      · rfl
      · have differ : (0 : Nat) = 1 := sameKey
        exact absurd differ (by decide)
    · rcases rightMember with rfl | rfl
      · have differ : (1 : Nat) = 0 := sameKey
        exact absurd differ (by decide)
      · rfl

/-! ## Selecting from it -/

/-- Looking up the gzip specification finds the gzip entry. -/
def gzipLookup : ExactStandardRealizerLookup stdlib gzipEntry.spec :=
  lookup_of_own_entry stdlib gzipEntry (by simp [stdlib])

/-- **And it is the realization it names.** -/
theorem gzip_lookup_realizes : gzipLookup.entry.realization = "gzip" := rfl

/--
**Any two lookups of the gzip specification select the same entry.**

§4's application-side promise: `ProcessRealization.standard
(lookupExact spec)` is one expression naming one program, not one expression
choosing among several.
-/
theorem selecting_gzip_is_forced
    (left right : ExactStandardRealizerLookup stdlib gzipEntry.spec) :
    left.entry = right.entry :=
  ExactStandardRealizerLookup.selection_is_determined left right

/-- So they agree on the program, not merely on the key. -/
theorem selecting_gzip_gives_one_program
    (left right : ExactStandardRealizerLookup stdlib gzipEntry.spec) :
    left.entry.realization = right.entry.realization :=
  ExactStandardRealizerLookup.realization_is_determined left right

/-! ## And what §4's stated law alone permits -/

/-- Two entries agreeing on specification and key, carrying different programs. -/
def twin (program : String) : StandardRealizerEntry SpecName Nat String := ⟨0, 0, program⟩

/--
A registry with §4's stated law and nothing else.

Declared here rather than reused from the module, because
`StandardRealizerRegistry` requires `keysDistinct` and the point is what happens
without it. Every clause §4 states holds of `entries`.
-/
structure SectionFourRegistry where
  /-- What is registered. -/
  entries : List (StandardRealizerEntry SpecName Nat String)
  /-- §4's law, in full: one specification, one key. -/
  unique : ∀ left ∈ entries, ∀ right ∈ entries,
    left.spec = right.spec → left.key = right.key

/-- A lookup against it, with every field §4 gives one. -/
structure SectionFourLookup (registry : SectionFourRegistry) (spec : SpecName) where
  /-- The entry selected. -/
  entry : StandardRealizerEntry SpecName Nat String
  /-- It is registered. -/
  member : entry ∈ registry.entries
  /-- And it realizes this specification. -/
  exactSpec : entry.spec = spec
  /-- And every matching entry selects the same key. -/
  unique : ∀ other ∈ registry.entries, other.spec = spec → other.key = entry.key

/-- The twins, registered. -/
def sectionFourStdlib : SectionFourRegistry where
  entries := [twin "alpha", twin "beta"]
  unique := by
    rintro left leftMember right rightMember _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at leftMember rightMember
    rcases leftMember with rfl | rfl <;> rcases rightMember with rfl | rfl <;> rfl

/-- One legal lookup of specification `0`. -/
def alphaLookup : SectionFourLookup sectionFourStdlib 0 where
  entry := twin "alpha"
  member := by simp [sectionFourStdlib]
  exactSpec := rfl
  unique := by
    rintro other otherMember _
    simp only [sectionFourStdlib, List.mem_cons, List.not_mem_nil, or_false] at otherMember
    rcases otherMember with rfl | rfl <;> rfl

/-- And another, equally legal. -/
def betaLookup : SectionFourLookup sectionFourStdlib 0 where
  entry := twin "beta"
  member := by simp [sectionFourStdlib]
  exactSpec := rfl
  unique := by
    rintro other otherMember _
    simp only [sectionFourStdlib, List.mem_cons, List.not_mem_nil, or_false] at otherMember
    rcases otherMember with rfl | rfl <;> rfl

/--
**Two legal lookups of one specification, selecting different programs.**

The reason `keysDistinct` is a field. §4's law says one specification implies
one *key*; two entries can share a key, share a specification, and differ in the
program they register, and every clause §4 states — including the lookup's own
uniqueness — holds of both selections.

So `ProcessRealization.standard (lookupExact spec)` would be one expression
denoting whichever of two programs the lookup happened to return, which is
exactly what §4 introduces the registry to prevent.

A first version of this fixture stated a predicate over a bare `List`, with no
registry, no lookup and no selection in it — the billed teeth were entirely in
the docstring. Local adversarial review pointed that out and showed the real
version was constructible; this is it.
-/
theorem section_four_uniqueness_alone_permits_two_realizations :
    alphaLookup.entry.realization ≠ betaLookup.entry.realization := by decide

/-- And that list does fail `keysDistinct`, which is what rules it out. -/
theorem the_twins_fail_the_added_law :
    ¬ (∀ left ∈ [twin "alpha", twin "beta"], ∀ right ∈ [twin "alpha", twin "beta"],
      left.key = right.key → left = right) := by
  intro distinct
  have same := distinct (twin "alpha") (by simp) (twin "beta") (by simp) rfl
  have programs : "alpha" = "beta" :=
    congrArg StandardRealizerEntry.realization same
  exact absurd programs (by decide)

end Grass.Process.Tests.Standard
