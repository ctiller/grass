import Grass.Platform.Win32.CoffLayout

/-!
# When an object file is internally consistent

Every module so far makes one record right. This says the records agree with
each other.

The distinction matters because a COFF object is a graph disguised as a byte
stream: a relocation names a symbol by index, a symbol names a section by
number, a `.pdata` entry names an offset into `.xdata`. Each of those is a bare
integer, and each layer's own theorems say nothing about whether it points at
anything. An object can be perfectly well-formed record by record and describe a
graph with dangling edges.

## What a dangling edge does

None of these produce a diagnostic. A relocation whose symbol index is past the
end of the table is read as whatever bytes follow it -- the string table, if the
symbol table ends there. A symbol claiming section seven of five resolves
against nothing. Neither is a link error in any tool this profile has measured;
they are silent corruption, which is why they are worth a predicate rather than
a comment.

## What this does not cover

Nothing here says the object is *useful*: a file whose every relocation is
in-range and whose every section number exists can still describe the wrong
program. These are the internal-consistency conditions, not correctness.

Nor does it cover `.pdata`'s ordering, which
`Grass/ABI/Win64/UnwindBytes.lean` states over linked addresses this layer does
not have.
-/

namespace Grass.Platform.Win32.Coff

/-! ## Section numbers -/

/--
A section number this object can resolve.

The three reserved values are always resolvable -- `undefined` is a promise to
another object, and the other two name no section by design. A real index has
to be in range, and COFF numbers sections from one, so zero is not an index but
the `undefined` marker.
-/
abbrev SectionNumber.ResolvableIn (n : SectionNumber)
    (sectionCount : Nat) : Prop :=
  match n with
  | .undefined => True
  | .absolute => True
  | .debug => True
  | .section_ i => 0 < i ∧ i ≤ sectionCount

/--
Resolvability is decidable.

Written out rather than derived: `ResolvableIn` matches on the section number,
which does not reduce while that number is a variable, so instance search
cannot find the instance on its own. Without this, a well-formedness check over
a concrete object cannot be evaluated -- it would have to be proved by hand for
every symbol, which is how a check stops being run. -/
instance (n : SectionNumber) (count : Nat) :
    Decidable (n.ResolvableIn count) := by
  cases n <;> simp only [SectionNumber.ResolvableIn] <;> infer_instance
/-- **The reserved numbers resolve against any object, including an empty one.**

They name no section, so there is nothing for them to be out of range of. -/
theorem SectionNumber.reserved_resolvable (count : Nat) :
    SectionNumber.undefined.ResolvableIn count
    ∧ SectionNumber.absolute.ResolvableIn count
    ∧ SectionNumber.debug.ResolvableIn count :=
  ⟨trivial, trivial, trivial⟩

/-- **Section zero is not a section.**

The case a bare `BitVec 16` would let through: COFF numbers sections from one,
so an index of zero is the `undefined` marker and never a reference. -/
theorem SectionNumber.section_zero_unresolvable (count : Nat) :
    ¬ (SectionNumber.section_ 0).ResolvableIn count := by
  intro h
  exact absurd h.1 (Nat.lt_irrefl 0)

/-- **A section number past the end does not resolve.** -/
theorem SectionNumber.section_past_end_unresolvable {i count : Nat}
    (h : count < i) : ¬ (SectionNumber.section_ i).ResolvableIn count := by
  intro hc
  simp only [SectionNumber.ResolvableIn] at hc
  omega

/-! ## The object's own consistency -/

/--
Every relocation in a section names a symbol the table has.

The index is into *records*, so an object with auxiliary records has a larger
bound than its symbol count -- which is the arithmetic `SymbolEntry` exists to
get right, checked here rather than assumed.
-/
abbrev Section.RelocationsInRange (s : Section) (recordCount : Nat) : Prop :=
  ∀ r ∈ s.relocations, r.symbolIndex.toNat < recordCount

/-- Every symbol names a section the object has, or a reserved value. -/
abbrev SymbolEntry.SectionResolvable (e : SymbolEntry)
    (sectionCount : Nat) : Prop :=
  e.symbol.sectionNumber.ResolvableIn sectionCount

/--
An object whose internal references all resolve.

Three conditions, and each corresponds to one kind of edge in the graph the
file describes.
-/
structure Object.WellFormed (o : Object) : Prop where
  /-- No relocation points past the symbol table. -/
  relocationsInRange :
    ∀ s ∈ o.sections, s.RelocationsInRange (symbolRecordCount o.symbols)
  /-- No symbol names a section that does not exist. -/
  symbolsResolvable :
    ∀ e ∈ o.symbols, e.SectionResolvable o.sections.length
  /-- Every auxiliary record describes a section the object actually has.
  A record defining a section absent from the file is a definition of nothing,
  and its size and relocation count would be a second, unrelated section's. -/
  auxDescribesOwnSection :
    ∀ e ∈ o.symbols, ∀ p ∈ e.aux, p.2 ∈ o.sections

/--
**An object with no sections, no symbols and no strings is well formed.**

The base case, and worth stating: every condition is a `∀` over an empty list,
so a predicate that had accidentally been stated as an existential would fail
here rather than silently accepting everything. -/
theorem Object.empty_wellFormed (m : Machine) :
    Object.WellFormed ⟨m, [], [], []⟩ where
  relocationsInRange := by intro s hs; simp at hs
  symbolsResolvable := by intro e he; simp at he
  auxDescribesOwnSection := by intro e he; simp at he

/--
**A relocation naming a record past the table breaks well-formedness.**

The falsifying case. Without it `WellFormed` could be a predicate that holds of
everything, which is the failure mode a structure of universals invites. -/
theorem Object.outOfRange_not_wellFormed (m : Machine) (nm : SectionName)
    (chs : BitVec 32) :
    ¬ Object.WellFormed
        ⟨m, [⟨nm, [], [⟨0, 7, .addr32nb⟩], chs⟩], [], []⟩ := by
  intro h
  have := h.relocationsInRange ⟨nm, [], [⟨0, 7, .addr32nb⟩], chs⟩ (by simp)
  have h7 := this ⟨0, 7, .addr32nb⟩ (by simp)
  simp [symbolRecordCount] at h7

end Grass.Platform.Win32.Coff
