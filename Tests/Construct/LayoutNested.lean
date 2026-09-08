import Grass.Construct.Layout.Nested

namespace Grass.Tests.Construct.LayoutNested

open Grass Grass.Core Grass.Memory Grass.Construct.Layout

private def profile : LayoutProfile :=
  ⟨fun alignment => alignment = 1 || alignment = 4 || alignment = 8⟩

private def field (name : String) (size alignment offset : Nat) :
    PlacedField profile :=
  ⟨⟨⟨name⟩, ⟨size, alignment⟩⟩, offset⟩

private def innerX := field "x" 4 4 0
private def innerY := field "y" 4 4 4
private def inner : StructLayout profile :=
  ⟨[innerX, innerY], 8, 8⟩

private def header := field "header" 8 8 0
private def parent := field "nested" 8 8 8
private def suffix := field "suffix" 8 8 16
private def outer : StructLayout profile :=
  ⟨[header, parent, suffix], 24, 8⟩

private def nestedY : NestedPlacement outer inner :=
  ⟨parent, by simp [outer], innerY, by simp [inner], rfl, rfl⟩

private def nestedX : NestedPlacement outer inner :=
  ⟨parent, by simp [outer], innerX, by simp [inner], rfl, rfl⟩

example : outer.WellFormed := by native_decide
example : inner.WellFormed := by native_decide
example : nestedY.byteRange = ⟨12, 4⟩ := rfl
example : translateRange 24 (translateRange 8 innerY.byteRange) =
    translateRange 32 innerY.byteRange :=
  translateRange.compose 24 8 innerY.byteRange
example : (translateRange 8 ⟨0, 8⟩).Contains (translateRange 8 ⟨4, 4⟩) :=
  translateRange.contains 8 (by native_decide)
example : (translateRange 8 innerX.byteRange).Disjoint
    (translateRange 8 innerY.byteRange) :=
  translateRange.disjoint 8 (by native_decide)
example : parent.byteRange.Contains nestedY.byteRange :=
  nestedY.containedInParent (by native_decide)
example : nestedY.byteRange.WithinBound outer.size :=
  nestedY.withinOuter (by native_decide) (by native_decide)
example : header.byteRange.Disjoint nestedY.byteRange :=
  nestedY.disjointOfParentDisjoint (by native_decide) (by native_decide)
example : nestedX.byteRange.Disjoint nestedY.byteRange :=
  nestedX.disjointOfChildDisjoint nestedY rfl (by native_decide)
example : nestedY.byteRange.stop = parent.offset + innerY.byteRange.stop :=
  nestedY.byteRange_stop
example : IsAligned nestedY.byteRange.start innerY.field.repr.alignment :=
  nestedY.aligned (by native_decide) (by native_decide)

end Grass.Tests.Construct.LayoutNested
