import Grass.Shader.WGSL.Composite

namespace Tests.Shader.WGSL.Composite

open Grass.Shader.WGSL.Composite

abbrev Lane := Nat

def a : Operand Lane := { scalar := .f32, width := 3, lanes := fun i => 10 + i.val }
def b : Operand Lane := { scalar := .f32, width := 4, lanes := fun i => 20 + i.val }
def scalar : Operand Lane := { scalar := .f32, width := 1, lanes := fun _ => 30 }
def signed : Operand Lane := { scalar := .i32, width := 3, lanes := fun i => 40 + i.val }

def aName : Identifier := { index := 0 }
def bName : Identifier := { index := 1 }
def scalarName : Identifier := { index := 2 }
def signedName : Identifier := { index := 3 }

def environment : Identifier → Option (Operand Lane)
  | { index := 0 } => some a
  | { index := 1 } => some b
  | { index := 2 } => some scalar
  | { index := 3 } => some signed
  | _ => none

def source : Source :=
  { first := { name := aName, lane := 2 }
    second := { name := bName, lane := 0 }
    third := { name := aName, lane := 1 }
    fourth := { name := bName, lane := 3 } }

example : parse? (write source) = some source := parse_write source

example : writeText source = "vec4<f32>(v0[2u],v1[0u],v0[1u],v1[3u])" := by
  rfl

example : check? environment (write source) = some { x := 12, y := 20, z := 11, w := 23 } := by
  rfl

/-- A scalar operand is refused even though its lane exists. -/
example : check? environment (write
    { first := { name := scalarName, lane := 0 }
      second := { name := bName, lane := 0 }
      third := { name := aName, lane := 0 }
      fourth := { name := bName, lane := 0 } }) = none := by
  rfl

/-- Integer vectors do not mix into this explicitly f32 constructor fragment. -/
example : check? environment (write
    { first := { name := signedName, lane := 0 }
      second := { name := bName, lane := 0 }
      third := { name := aName, lane := 0 }
      fourth := { name := bName, lane := 0 } }) = none := by
  rfl

/-- Out-of-range lane selection is refused. -/
example : check? environment (write
    { first := { name := aName, lane := 3 }
      second := { name := bName, lane := 0 }
      third := { name := aName, lane := 0 }
      fourth := { name := bName, lane := 0 } }) = none := by
  rfl

/-- Wrong constructor/type token sequences do not parse. -/
example : parse? [.vec4, .lt, .i32, .gt, .lparen, .ident aName, .lbracket, .uintLiteral 0,
    .rbracket, .rparen] = none := by
  rfl

end Tests.Shader.WGSL.Composite
