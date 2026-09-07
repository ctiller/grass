import Grass.Construct.Layout.Core

/-!
# Checked ordinary-struct derivation

`deriveStruct` places fields deterministically in declaration order, inserting
the minimum alignment padding before each field and at aggregate tail.  Success
returns `CheckedStructLayout`, whose `valid` field is the executable checker
result as a proposition; malformed input or an unexpected derived candidate is
returned as a typed error.
-/

namespace Grass.Construct.Layout

open Grass.Core

/-- Why ordinary struct derivation did not return a checked layout. -/
inductive StructDerivationError where
  | emptyFields
  | duplicateNames (names : List Name)
  | invalidField (index : Nat)
  | invalidAggregateAlignment (alignment : Nat)
  | aggregateAlignmentTooWeak (fieldIndex : Nat)
  | candidateRejected
deriving Repr, DecidableEq

/-- Ordinary layout paired with its checked structural certificate. -/
structure CheckedStructLayout (profile : LayoutProfile) where
  layout : StructLayout profile
  valid : layout.WellFormed

/-- Smallest value at least `value` aligned to a positive `alignment`.
Callers that need a checked guarantee use `deriveStruct`, which rejects zero. -/
def alignUp (value alignment : Nat) : Nat :=
  value + (alignment - value % alignment) % alignment

private def placeFrom {profile : LayoutProfile} :
    Nat → List (FieldSpec profile) → List (PlacedField profile) × Nat
  | cursor, [] => ([], cursor)
  | cursor, field :: rest =>
      let offset := alignUp cursor field.repr.alignment
      let placed := ⟨field, offset⟩
      let tail := placeFrom (offset + field.repr.size) rest
      (placed :: tail.1, tail.2)

/-- Deterministic unchecked candidate used internally before the defensive
`StructLayout.wellFormed` post-check. -/
def deriveCandidate {profile : LayoutProfile} (aggregateAlignment : Nat)
    (fields : List (FieldSpec profile)) : StructLayout profile :=
  let placed := placeFrom 0 fields
  {
    fields := placed.1
    size := alignUp placed.2 aggregateAlignment
    alignment := aggregateAlignment
  }

private def firstInvalidField? {profile : LayoutProfile} :
    Nat → List (FieldSpec profile) → Option Nat
  | _, [] => none
  | index, field :: rest =>
      if 0 < field.repr.size ∧ field.repr.WellFormed then
        firstInvalidField? (index + 1) rest
      else
        some index

private def firstTooStrongAlignment? {profile : LayoutProfile} :
    Nat → Nat → List (FieldSpec profile) → Option Nat
  | _, _, [] => none
  | aggregateAlignment, index, field :: rest =>
      if aggregateAlignment % field.repr.alignment = 0 then
        firstTooStrongAlignment? aggregateAlignment (index + 1) rest
      else
        some index

/-- Derive and check one ordinary nonempty struct layout. -/
def deriveStruct {profile : LayoutProfile} (aggregateAlignment : Nat)
    (fields : List (FieldSpec profile)) :
    Except StructDerivationError (CheckedStructLayout profile) :=
  if _empty : fields = [] then
    .error .emptyFields
  else if _unique : (fields.map FieldSpec.name).Nodup then
    match firstInvalidField? 0 fields with
    | some index => .error (.invalidField index)
    | none =>
        if _aggregateValid : 0 < aggregateAlignment ∧
            profile.acceptsAlignment aggregateAlignment = true then
          match firstTooStrongAlignment? aggregateAlignment 0 fields with
          | some index => .error (.aggregateAlignmentTooWeak index)
          | none =>
              let candidate := deriveCandidate aggregateAlignment fields
              if valid : candidate.WellFormed then
                .ok ⟨candidate, valid⟩
              else
                .error .candidateRejected
        else
          .error (.invalidAggregateAlignment aggregateAlignment)
  else
    .error (.duplicateNames (fields.map FieldSpec.name))

end Grass.Construct.Layout
