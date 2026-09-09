import Lean
import Grass.Frontend.Source

/-!
# Authored assembly command syntax

This module captures the current Hello declaration losslessly and elaborates
it through the existing checked source producers.
-/

namespace Grass.Frontend.AssemblySyntax

open Lean Parser Elab Command

/-- Consume the current assembly body as one lossless atom.  Spike 1's body
contains no braces; the closing brace therefore terminates this narrow parser.
The atom's source information retains the original body characters. -/
def assemblyBody : Parser where
  fn := rawFn (takeUntilFn (fun c => c = '}'))

@[combinator_formatter assemblyBody]
def assemblyBodyFormatter : Lean.PrettyPrinter.Formatter :=
  Lean.PrettyPrinter.Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer assemblyBody]
def assemblyBodyParenthesizer : Lean.PrettyPrinter.Parenthesizer :=
  Lean.PrettyPrinter.Parenthesizer.visitToken

/-- Internal handoff from the lossless command parser to the checked source
elaborator.  Its arguments are the exact declaration text, selected plan, and
evaluated static-object table.  The hook converts the literal directly to the
logical character list expected by source construction. -/
syntax (name := machineSourceCapture)
  "__grass_machine_source_capture" "(" term "," term "," term ")" : term

/-- The elaborator only constructs a proof term checked by Lean's kernel.
Source text becomes literal data; no file read or native proof authority is used. -/
elab_rules : term
  | `(__grass_machine_source_capture ($source:str, $plan, $statics)) => do
      let chars ← Lean.Elab.Term.exprToSyntax (toExpr source.getString.toList)
      let result ← `(term|
        (Grass.MachineSource.ofHello? $plan $chars $statics).get
          (by
            set_option maxRecDepth 100000 in
            set_option maxHeartbeats 16000000 in
            decide +kernel))
      Lean.Elab.Term.elabTerm result none

/-- The intentionally narrow first `asm_source` command surface.  Wrapper and
body spelling is captured from the original command rather than reconstructed
from pretty-printed syntax. -/
@[command_parser] def helloAssemblyDefinition : Parser := leading_parser
  "def" >> ident >> ":" >> nonReservedSymbol "MachineSource" true >> ident >> ":=" >>
  nonReservedSymbol "withStack" true >> "(" >> ident >> ":" >>
    nonReservedSymbol "UInt32" true >> ":=" >> Parser.Term.num >> ")" >>
  nonReservedSymbol "withCallFrame" true >> ident >>
    nonReservedSymbol "asm_source" true >>
  "(" >> nonReservedSymbol "statics" true >> ":=" >> ident >> ")" >>
  "{" >> assemblyBody >> "}"

private def exactSource (stx : Syntax) : CommandElabM String := do
  let some start := stx.getPos? (canonicalOnly := true)
    | throwErrorAt stx "assembly declaration has no original source start"
  let some finish := stx.getTailPos? (canonicalOnly := true)
    | throwErrorAt stx "assembly declaration has no original source end"
  let fileMap ← getFileMap
  return String.Pos.Raw.extract fileMap.source start finish

/-- Identifiers in this fixed command grammar are direct children; the raw
assembly body is an atom and never contributes identifiers to this selection. -/
private def identifiers (stx : Syntax) : List Syntax :=
  stx.getArgs.toList.filter Syntax.isIdent

@[command_elab Grass.Frontend.AssemblySyntax.helloAssemblyDefinition]
def elabHelloAssemblyDefinition : CommandElab := fun stx => do
    let ids := identifiers stx
    let triple ← match ids with
      | name :: plan :: _local :: _callFrame :: staticSyntax :: [] =>
          pure (name, plan, staticSyntax)
      | _ => throwErrorAt stx "malformed assembly declaration capture"
    let name : Ident := ⟨triple.1⟩
    let plan : Term := ⟨triple.2.1⟩
    let staticTerm : Term := ⟨triple.2.2⟩
    let machineSource : Term := ⟨mkIdent `Grass.MachineSource⟩
    let authored := Syntax.mkStrLit (← exactSource stx)
    let expanded ← `(command|
      def $name : $machineSource $plan :=
        __grass_machine_source_capture ($authored, $plan, $staticTerm))
    elabCommand expanded

end Grass.Frontend.AssemblySyntax
