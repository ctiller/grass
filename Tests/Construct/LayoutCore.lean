import Grass.Construct.Layout.Core

/-!
# Physical layout core fixtures

The good example contains real alignment padding. Negative fixtures pin every
independent condition of `StructLayout.wellFormed`; a malformed alignment may
also fail a dependent compatibility check.
-/

namespace Grass.Tests.Construct.LayoutCore

open Grass.Core Grass.Construct.Layout

def profile : LayoutProfile where
  acceptsAlignment := fun alignment => [1, 2, 4, 8, 16].contains alignment

def u8 : ObjectRepr profile := ⟨1, 1⟩
def u32 : ObjectRepr profile := ⟨4, 4⟩

def field (name : String) (repr : ObjectRepr profile) (offset : Nat) :
    PlacedField profile :=
  ⟨⟨⟨name⟩, repr⟩, offset⟩

/-- One byte at offset zero, three bytes of padding, then a four-byte field. -/
def good : StructLayout profile where
  fields := [field "tag" u8 0, field "value" u32 4]
  size := 8
  alignment := 4

example : good.WellFormed := by decide
example : good.lookup? ⟨"value"⟩ = some (field "value" u32 4) := by decide

def duplicateName : StructLayout profile where
  fields := [field "value" u8 0, field "value" u32 4]
  size := 8
  alignment := 4

example : ¬ duplicateName.WellFormed := by decide

def misalignedField : StructLayout profile where
  fields := [field "tag" u8 0, field "value" u32 2]
  size := 8
  alignment := 4

example : ¬ misalignedField.WellFormed := by decide

def overlappingFields : StructLayout profile where
  fields := [field "left" u32 0, field "right" u32 0]
  size := 8
  alignment := 4

example : ¬ overlappingFields.WellFormed := by decide

def fieldPastEnd : StructLayout profile where
  fields := [field "value" u32 4]
  size := 7
  alignment := 1

example : ¬ fieldPastEnd.WellFormed := by decide

def zeroFieldAlignment : StructLayout profile where
  fields := [field "value" ⟨4, 0⟩ 0]
  size := 4
  alignment := 4

example : ¬ zeroFieldAlignment.WellFormed := by decide

def zeroSizedField : StructLayout profile where
  fields := [field "empty" ⟨0, 1⟩ 0]
  size := 0
  alignment := 1

example : ¬ zeroSizedField.WellFormed := by decide

def emptyAggregate : StructLayout profile where
  fields := []
  size := 0
  alignment := 1

example : ¬ emptyAggregate.WellFormed := by decide

def rejectedAggregateAlignment : StructLayout profile where
  fields := [field "value" u8 0]
  size := 3
  alignment := 3

example : ¬ rejectedAggregateAlignment.WellFormed := by decide

def aggregateTooWeak : StructLayout profile where
  fields := [field "value" u32 0]
  size := 4
  alignment := 2

example : ¬ aggregateTooWeak.WellFormed := by decide

def aggregateSizeMisaligned : StructLayout profile where
  fields := [field "tag" u8 0]
  size := 3
  alignment := 2

example : ¬ aggregateSizeMisaligned.WellFormed := by decide

end Grass.Tests.Construct.LayoutCore
