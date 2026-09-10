import Lean
import Grass.Frontend.Source

/-! Exact command syntax capture for checked structural assembly construction. -/
namespace Grass.Frontend.AssemblySyntax
open Lean Parser Elab Command

/-- Scan balanced braces without treating quoted text or comments as delimiters. -/
partial def bodyFn (depth : Nat) (quoted escaped lineComment : Bool) (block : Nat) : ParserFn := fun c s =>
  let pos := s.pos
  if h : c.atEnd pos then s.mkUnexpectedError "unterminated assembly body"
  else
    let ch := c.get' pos h
    let next := s.next' c pos h
    let following := c.get next.pos
    if lineComment then bodyFn depth false false (ch != '\n') 0 c next
    else if block > 0 then
      if ch == '/' && following == '-' then bodyFn depth false false false (block + 1) c (next.next c next.pos)
      else if ch == '-' && following == '/' then bodyFn depth false false false (block - 1) c (next.next c next.pos)
      else bodyFn depth false false false block c next
    else if quoted then
      if escaped then bodyFn depth true false false 0 c next
      else if ch == '\\' then bodyFn depth true true false 0 c next
      else bodyFn depth (ch != '"') false false 0 c next
    else if ch == '-' && following == '-' then bodyFn depth false false true 0 c (next.next c next.pos)
    else if ch == '/' && following == '-' then bodyFn depth false false false 1 c (next.next c next.pos)
    else if ch == '"' then bodyFn depth true false false 0 c next
    else if ch == '{' then bodyFn (depth + 1) false false false 0 c next
    else if ch == '}' then
      if depth == 0 then s else bodyFn (depth - 1) false false false 0 c next
    else bodyFn depth false false false 0 c next

def assemblyBody : Parser where
  fn := rawFn (bodyFn 0 false false false 0)

@[combinator_formatter assemblyBody]
def assemblyBodyFormatter : Lean.PrettyPrinter.Formatter :=
  Lean.PrettyPrinter.Formatter.visitAtom Name.anonymous
@[combinator_parenthesizer assemblyBody]
def assemblyBodyParenthesizer : Lean.PrettyPrinter.Parenthesizer :=
  Lean.PrettyPrinter.Parenthesizer.visitToken

declare_syntax_cat assemblyLocal
syntax "withStack" "(" ident ":" ident ":=" num ")" : assemblyLocal
syntax (name := assemblyDefinition)
  "def" ident ":" &"MachineSource" ident ":=" assemblyLocal*
  &"withCallFrame" ident &"asm_source" "(" &"statics" ":=" ident ")"
  "{" assemblyBody "}" : command

syntax (name := machineSourceCapture)
  "__grass_machine_source_capture" "(" term "," term "," term "," term ")" : term

/-- Literal input and ranges are checked in the kernel by the same producer
used independently of elaboration. No file IO or executable proof authority. -/
elab_rules : term
  | `(__grass_machine_source_capture ($source:str, $offsets, $plan, $statics)) => do
      let chars ← Lean.Elab.Term.exprToSyntax (toExpr source.getString.toList)
      let result ← `(term|
        (Grass.MachineSource.ofSource? $plan $chars $offsets $statics).get
          (by
            set_option maxRecDepth 100000 in
            set_option maxHeartbeats 16000000 in
            decide +kernel))
      Lean.Elab.Term.elabTerm result none

private def originalStart (stx : Syntax) : CommandElabM String.Pos.Raw := do
  let some pos := stx.getPos? (canonicalOnly := true)
    | throwErrorAt stx "assembly syntax has no original source start"
  return pos
private def originalEnd (stx : Syntax) : CommandElabM String.Pos.Raw := do
  let some pos := stx.getTailPos? (canonicalOnly := true)
    | throwErrorAt stx "assembly syntax has no original source end"
  return pos

@[command_elab assemblyDefinition]
def elabAssemblyDefinition : CommandElab := fun stx => do
  -- Destructure the command grammar, whose repeated locals form one syntax node.
  -- Identifier counts and local names do not determine the selected plan/table.
  let #[_, nameSyntax, _, _, planSyntax, _, localsSyntax, _, _, _, _, _, _, staticSyntax,
      _, opening, _, closing] := stx.getArgs
    | throwErrorAt stx "malformed assembly command syntax"
  for localSyntax in localsSyntax.getArgs do
    match localSyntax with
    | `(assemblyLocal| withStack ($_name:ident : $localType:ident := $_value:num)) =>
      unless localType.getId == `UInt32 do
        throwErrorAt localType "unsupported stack-local type; this construction backend supports UInt32"
    | _ => throwErrorAt localSyntax "malformed stack-local declaration"
  let name : Ident := ⟨nameSyntax⟩
  let plan : Term := ⟨planSyntax⟩
  let statics : Term := ⟨staticSyntax⟩
  let start ← originalStart stx
  let finish ← originalEnd stx
  let headerStart ← originalEnd nameSyntax
  let headerFinish ← originalStart opening
  let bodyStart ← originalEnd opening
  let bodyFinish ← originalStart closing
  let source := (← getFileMap).source
  let relative (pos : String.Pos.Raw) : Nat :=
    (String.Pos.Raw.extract source start pos).toList.length
  let hs := Syntax.mkNumLit (toString (relative headerStart))
  let hf := Syntax.mkNumLit (toString (relative headerFinish))
  let bs := Syntax.mkNumLit (toString (relative bodyStart))
  let bf := Syntax.mkNumLit (toString (relative bodyFinish))
  let offsets ← `(term| Grass.Assembly.SourceInput.SourceOffsets.mk $hs $hf $bs $bf)
  let authored := Syntax.mkStrLit (String.Pos.Raw.extract source start finish)
  let machineSource : Term := ⟨mkIdent `Grass.MachineSource⟩
  let expanded ← `(command|
    def $name : $machineSource $plan :=
      __grass_machine_source_capture ($authored, $offsets, $plan, $statics))
  elabCommand expanded

end Grass.Frontend.AssemblySyntax
