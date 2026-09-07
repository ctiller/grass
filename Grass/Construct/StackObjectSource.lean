import Grass.Construct.Fragment.Source
import Grass.Construct.StackObject

/-!
# Transparent checked stack-object sources

`StackObjectSourceBackend` is the machine-owned boundary for loading and
storing checked object slices. Construction passes only the slice's derived
absolute range to the backend and wraps the returned instructions as an
inspectable `Fragment.Source`; this layer supplies no semantic certificate.
-/

namespace Grass.Construct

open Grass.Memory Grass.Construct.Layout Grass.Construct.Fragment

universe u v

/-- Machine-specific constructors for operations over exact stack byte ranges. -/
structure StackObjectSourceBackend (Instruction : Type u) (Operand : Type v) where
  loadAt : ByteRange → Operand → List Instruction
  storeAt : ByteRange → Operand → List Instruction

namespace StackObjectSourceBackend

variable {Instruction : Type u} {Operand : Type v}
  {profile : LayoutProfile} {checked : CheckedStackLayout profile}
  {slot : StackObjectRef checked}

/-- Transparent source for loading one checked slice. -/
def load (backend : StackObjectSourceBackend Instruction Operand)
    (slice : CheckedStackSlice slot) (destination : Operand) : Source Instruction :=
  .literal (backend.loadAt slice.absoluteRange destination)

/-- Transparent source for storing one checked slice. -/
def store (backend : StackObjectSourceBackend Instruction Operand)
    (slice : CheckedStackSlice slot) (source : Operand) : Source Instruction :=
  .literal (backend.storeAt slice.absoluteRange source)

/-- Transparent nominal projection for loading one checked slice. -/
def loadNamed (backend : StackObjectSourceBackend Instruction Operand)
    {name : Grass.Core.Name} (slice : NamedCheckedStackSlice checked name)
    (destination : Operand) : Source Instruction :=
  backend.load slice.checkedSlice destination

/-- Transparent nominal projection for storing one checked slice. -/
def storeNamed (backend : StackObjectSourceBackend Instruction Operand)
    {name : Grass.Core.Name} (slice : NamedCheckedStackSlice checked name)
    (source : Operand) : Source Instruction :=
  backend.store slice.checkedSlice source

@[simp] theorem load_expand (backend : StackObjectSourceBackend Instruction Operand)
    (slice : CheckedStackSlice slot) (destination : Operand) :
    (backend.load slice destination).expand =
      backend.loadAt slice.absoluteRange destination := by
  simp [load]

@[simp] theorem store_expand (backend : StackObjectSourceBackend Instruction Operand)
    (slice : CheckedStackSlice slot) (source : Operand) :
    (backend.store slice source).expand =
      backend.storeAt slice.absoluteRange source := by
  simp [store]

@[simp] theorem loadNamed_expand
    (backend : StackObjectSourceBackend Instruction Operand)
    {name : Grass.Core.Name} (slice : NamedCheckedStackSlice checked name)
    (destination : Operand) :
    (backend.loadNamed slice destination).expand =
      backend.loadAt slice.checkedSlice.absoluteRange destination := by
  simp [loadNamed]

@[simp] theorem storeNamed_expand
    (backend : StackObjectSourceBackend Instruction Operand)
    {name : Grass.Core.Name} (slice : NamedCheckedStackSlice checked name)
    (source : Operand) :
    (backend.storeNamed slice source).expand =
      backend.storeAt slice.checkedSlice.absoluteRange source := by
  simp [storeNamed]

end StackObjectSourceBackend

end Grass.Construct
