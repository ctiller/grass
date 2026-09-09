import Grass.Assembly.StaticObjects

namespace Grass.Tests.Assembly.StaticObjects

open Grass.Assembly.StaticObjects Grass.Std.Logical

def payload : Grass.Std.Logical.ByteArray := Vec.fromList [1, 2, 3]
def suffix : Grass.Std.Logical.ByteArray := Vec.fromList [4, 5]

/- These ordinary declarations check that DSL words remain non-reserved. -/
def bytes : Grass.Std.Logical.ByteArray := payload
def align : Nat := 8
def rodata : Nat := 1
def static_objects : Nat := 0

def statics : Grass.StaticObjectTable := static_objects {
  rodata align 8 {
    payload: bytes payload,
    combined: bytes (payload ++ suffix)
  }
}

def single : Grass.StaticObjectTable := static_objects {
  rodata align 1 {
    payload: bytes payload
  }
}

example : statics.declarations.map Declaration.name = ["payload", "combined"] := rfl
example : statics.declarations.map Declaration.alignment = [8, 8] := rfl
example : single.declarations.map Declaration.name = ["payload"] := rfl
example : (statics.lookup? "combined").map Declaration.bytes =
    some (payload ++ suffix) := by decide
example : ∀ declaration ∈ statics.declarations,
    statics.lookup? declaration.name = some declaration := by
  intro declaration member
  exact statics.lookup?_complete member
example : (statics.lookup? "combined").map
    (fun declaration => declaration.bytes.length) = some (payload.length + suffix.length) := by
  decide

def duplicateDeclarations : List Declaration :=
  [{ name := "payload", alignment := 1, kind := .rodata, bytes := payload },
   { name := "payload", alignment := 1, kind := .rodata, bytes := suffix }]

example : validate? duplicateDeclarations = none := by decide
example : validate?
    [{ name := "bad", alignment := 0, kind := .rodata, bytes := payload }] = none := by decide
example : validate?
    [{ name := "bad", alignment := 3, kind := .rodata, bytes := payload }] = none := by decide

end Grass.Tests.Assembly.StaticObjects
