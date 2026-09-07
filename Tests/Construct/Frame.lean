import Grass.Construct.Frame

namespace Grass.Tests.Construct.Frame

open Grass Grass.Core Grass.Construct Grass.Construct.Layout Grass.ISA.X86

private def profile : LayoutProfile := ⟨fun alignment => alignment = 8 || alignment = 16⟩
private def root : ScopeId := ⟨⟨"root"⟩⟩
private def layout : StackLayout profile :=
  ⟨[⟨root, none⟩], [⟨⟨"local"⟩, ⟨16, 16⟩, 0, root⟩], 16, 16, 128⟩

private def checked := deriveWin64Frame layout [.rbx, .r12] 16

example : checked.isOk = true := by native_decide
example : (deriveWin64Frame layout [.rsp] 0).isOk = false := by native_decide
example : (deriveWin64Frame layout [.rax] 0).isOk = false := by native_decide
example : (deriveWin64Frame layout [.rbx, .rbx] 0).isOk = false := by native_decide
example : (match deriveWin64Frame layout [] 7 with
    | .error (.invalidStackArgumentBytes 7) => true
    | _ => false) = true := by native_decide

end Grass.Tests.Construct.Frame
