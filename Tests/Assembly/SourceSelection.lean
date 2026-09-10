import Grass.Assembly.SourceInput

/-! Generic fixture tooling for selecting one marked declaration from authored file characters. -/

namespace Grass.Tests.Assembly.SourceSelection

open Grass.Assembly.SourceInput

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

private def markedBrace? (marker : String) : List Token → Option (Token × List Token)
  | [] => none
  | token :: rest => match token.kind with
    | .leftBrace => some (token, rest)
    | .word value => if value = marker || value = "def" then none else markedBrace? marker rest
    | .rightBrace => none
    | _ => markedBrace? marker rest

private def bodyEnd? : List Token → Nat → Option Token
  | [], _ => none
  | token :: rest, depth => match token.kind with
    | .leftBrace => bodyEnd? rest (depth + 1)
    | .rightBrace => if depth = 1 then some token else bodyEnd? rest (depth - 1)
    | _ => bodyEnd? rest depth

private def commandRange? (marker : String) (start : Nat) : List Token → Option (Nat × Nat)
  | [] => none
  | token :: rest => match token.kind with
    | .word value => if value = marker then do
        let (_, afterBrace) ← markedBrace? marker rest
        let close ← bodyEnd? afterBrace 1
        some (start, close.finish)
      else if value = "def" then none else commandRange? marker start rest
    | .rightBrace => none
    | _ => commandRange? marker start rest

private def matchingRanges (marker name : String) : List Token → List (Nat × Nat)
  | declaration :: declaredName :: rest =>
    let later := matchingRanges marker name (declaredName :: rest)
    match declaration.kind, declaredName.kind with
    | .word "def", .word actualName =>
      if actualName = name then
        match commandRange? marker declaration.start rest with
        | some range => range :: later
        | none => later
      else later
    | _, _ => later
  | _ => []

/-- A file-backed command slice and its exact half-open source range. -/
structure Selection (file : List Char) where
  start : Nat
  finish : Nat
  chars : List Char
  slice_eq : chars = (file.drop start).take (finish - start)

/-- Select the complete source range of exactly one `def name` using `marker`.
The shared tokenization handles comments, strings, and nested braces. -/
def selectCommand? (marker name : String) (file : List Char) : Option (Selection file) := do
  let tokens ← tokensChars file
  match matchingRanges marker name tokens with
  | [(start, finish)] => some ⟨start, finish, (file.drop start).take (finish - start), rfl⟩
  | _ => none

example : (selectCommand? "spirv_asm" "other" "def other := spirv_asm { /- } -/ \"{\" nested { } }".toList).map
    (fun selection => selection.chars) =
    some "def other := spirv_asm { /- } -/ \"{\" nested { } }".toList := by decide
example : selectCommand? "spirv_asm" "same"
    "def same := spirv_asm { first }\ndef same := spirv_asm { second }".toList = none := by decide

end Grass.Tests.Assembly.SourceSelection
