import Grass.Construct.StackObject

/-!
# Checked stack-object fixtures

Fixtures pin nominal membership, relative and absolute ranges, layout
containment, and structured rejection of malformed requests.
-/

namespace Grass.Tests.Construct.StackObject

open Grass.Core Grass.Memory Grass.Construct Grass.Construct.Layout

private def profile : LayoutProfile := ⟨fun alignment => alignment = 8 || alignment = 16⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def word : Layout.StackObject profile :=
  ⟨⟨"word"⟩, ⟨8, 8⟩, 16, root⟩
private def layout : StackLayout profile :=
  ⟨[⟨root, none⟩], [word], 32, 16, 64⟩
private def checked : CheckedStackLayout profile := ⟨layout, by decide⟩
private def slot : StackObjectRef checked := ⟨word, by decide⟩
private def slice : CheckedStackSlice slot := ⟨⟨2, 4⟩, by decide⟩

example : checked.layout.objectWellFormed slot.object = true := slot.objectWellFormed
example : slot.object.byteRange.WithinBound checked.layout.size := slot.withinLayout
example : slice.slice.relativeRange = ⟨2, 4⟩ := rfl
example : slice.absoluteRange = ⟨18, 4⟩ := rfl
example : slice.absoluteRange.WithinBound checked.layout.size := slice.withinLayout

private def sliceRange
    (result : Except StackObjectError
      (NamedCheckedStackSlice checked ⟨"word"⟩)) :
    Except StackObjectError ByteRange :=
  result.map fun found => found.checkedSlice.absoluteRange

example : sliceRange (checkStackSlice checked ⟨"word"⟩ 2 4) = .ok ⟨18, 4⟩ := by
  rfl
example : match checkStackSlice checked ⟨"word"⟩ 2 4 with
    | .ok found => found.objectRef.slot.object.name = ⟨"word"⟩
    | .error _ => False := by
  rfl
example : (checkStackSlice checked ⟨"missing"⟩ 0 1).map (fun _ => ()) =
    .error (.missingObject ⟨"missing"⟩) := by rfl
example : (checkStackSlice checked ⟨"word"⟩ 0 0).map (fun _ => ()) =
    .error .zeroSize := by rfl
example : (checkStackSlice checked ⟨"word"⟩ 6 4).map (fun _ => ()) =
    .error (.outOfBounds 6 4 8) := by rfl

private def invalidLayout : StackLayout profile :=
  ⟨[⟨root, none⟩], [word], 31, 16, 64⟩

example : (checkStackLayout invalidLayout).map (fun _ => ()) =
    .error .invalidLayout := by rfl

end Grass.Tests.Construct.StackObject
