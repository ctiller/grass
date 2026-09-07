import Grass.Construct.Layout.Derive
import Tests.Construct.LayoutCore

/-!
# Checked ordinary-layout derivation fixtures

Fixtures pin exact offsets and tail padding, then distinguish empty, duplicate,
invalid-field, invalid-aggregate, and too-weak aggregate-alignment failures.
-/

namespace Grass.Tests.Construct.LayoutDerive

open Grass Grass.Core Grass.Construct.Layout
open Grass.Tests.Construct.LayoutCore

def tagField : FieldSpec profile := ⟨⟨"tag"⟩, u8⟩

def fields : List (FieldSpec profile) := [
  tagField,
  ⟨⟨"value"⟩, u32⟩,
  ⟨⟨"tail"⟩, u8⟩
]

def derivedLayout? : Option (StructLayout profile) :=
  match deriveStruct 4 fields with
  | .ok checked => some checked.layout
  | .error _ => none

def derivationError (alignment : Nat) (input : List (FieldSpec profile)) :
    Option StructDerivationError :=
  match deriveStruct alignment input with
  | .ok _ => none
  | .error error => some error

example : derivedLayout?.map StructLayout.fieldNames =
    some [⟨"tag"⟩, ⟨"value"⟩, ⟨"tail"⟩] := by decide

example : derivedLayout?.map (fun layout =>
    (layout.fields.map PlacedField.offset, layout.size, layout.alignment)) =
    some ([0, 4, 8], 12, 4) := by decide

example : derivationError 4 [] = some .emptyFields := by decide
example : derivationError 4 [tagField, tagField] =
    some (.duplicateNames [⟨"tag"⟩, ⟨"tag"⟩]) := by decide
example : derivationError 4 [⟨⟨"bad"⟩, ⟨0, 1⟩⟩] =
    some (.invalidField 0) := by decide
example : derivationError 3 fields = some (.invalidAggregateAlignment 3) := by
  decide
example : derivationError 2 [⟨⟨"value"⟩, u32⟩] =
    some (.aggregateAlignmentTooWeak 0) := by decide

end Grass.Tests.Construct.LayoutDerive
