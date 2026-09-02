/-!
# Nominal names

An open nominal name with decidable equality.

`docs/INSTRUCTIONS.md` §1 and `docs/FOUNDATION.md` law 8 together rule out the
obvious alternative. A closed inductive of address spaces, fault classes,
obligation kinds, or resource axes would have to be edited by every profile that
introduces one, which is exactly the closed master sum type the corpus forbids.
A `Name` is instead minted by whoever owns the concept, and the well-known ones
are definitions rather than constructors.

Openness has a price and it is paid deliberately: nothing here prevents two
profiles from choosing the same string for different concepts. Uniqueness is a
registration property of the profile that declares a name, not a property of
this type. `docs/FOUNDATION.md` law 8 still applies to consumers, so an
unrecognized name is rejected rather than approximated.

**Custody note.** `Grass.Core` is not owned by the memory agent. This module is
temporary custody under `docs/MEMORY_IMPLEMENTATION_PLAN.md` §2.
-/

namespace Grass.Core

/--
An open nominal name.

`Name` is a distinct type rather than an abbreviation for `String` so that a
name cannot be silently confused with arbitrary text, and so that a later
representation change stays local.
-/
structure Name where
  /-- The name's text. -/
  text : String
deriving DecidableEq, Repr, Inhabited

namespace Name

instance : ToString Name := ⟨Name.text⟩

theorem eq_of_text_eq {a b : Name} (h : a.text = b.text) : a = b := by
  cases a; cases b; simp_all

end Name

end Grass.Core
