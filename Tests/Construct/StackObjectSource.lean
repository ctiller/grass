import Grass.Construct.StackObjectSource

/-!
# Transparent checked stack-object source fixtures

Fixtures pin exact relative-to-absolute range derivation for direct and named
load/store sources.
-/

namespace Grass.Tests.Construct.StackObjectSource

open Grass.Core Grass.Memory Grass.Construct Grass.Construct.Layout
  Grass.Construct.Fragment

private inductive Operand where
  | register (name : String)
deriving Repr, DecidableEq

private inductive Instruction where
  | load (range : ByteRange) (destination : Operand)
  | store (range : ByteRange) (source : Operand)
deriving Repr, DecidableEq

private def backend : StackObjectSourceBackend Instruction Operand where
  loadAt range destination := [.load range destination]
  storeAt range source := [.store range source]

private def profile : LayoutProfile :=
  ⟨fun alignment => alignment = 8 || alignment = 16⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def word : Layout.StackObject profile :=
  ⟨⟨"word"⟩, ⟨8, 8⟩, 16, root⟩
private def layout : StackLayout profile :=
  ⟨[⟨root, none⟩], [word], 32, 16, 64⟩
private def checked : CheckedStackLayout profile := ⟨layout, by native_decide⟩
private def slot : StackObjectRef checked := ⟨word, by decide⟩
private def slice : CheckedStackSlice slot := ⟨⟨2, 4⟩, by native_decide⟩
private def destination : Operand := .register "rax"
private def source : Operand := .register "rbx"

example : (backend.load slice destination).expand =
    [.load ⟨18, 4⟩ destination] := by native_decide
example : (backend.store slice source).expand =
    [.store ⟨18, 4⟩ source] := by native_decide

private def namedRef : CheckedStackLayout.NamedStackObjectRef checked ⟨"word"⟩ :=
  ⟨slot, rfl⟩
private def named : NamedCheckedStackSlice checked ⟨"word"⟩ :=
  ⟨namedRef, slice⟩

example : named.objectRef.slot.object.name = ⟨"word"⟩ := named.objectRef.nameExact
example : (backend.loadNamed named destination).expand =
    [.load ⟨18, 4⟩ destination] := by native_decide
example : (backend.storeNamed named source).expand =
    [.store ⟨18, 4⟩ source] := by native_decide

end Grass.Tests.Construct.StackObjectSource
