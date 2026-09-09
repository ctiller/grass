import Grass.Refinement.Console.WriteAllHead
import Tests.Assembly.SourceResolve

namespace Grass.Tests.Console.WriteAllHead

open Grass.Assembly

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Feed the current authored program through the same parser/frame/splice and
resolver used by the existing source fixture. No replacement program is built. -/
def selected (text : List Char) : Option Bool := do
    let symbols ← Grass.Tests.Assembly.SourceResolve.checkedSymbols
    let body ← (SourceInput.extractHelloSourceChars text).toOption
    let frame ← SourceFrame.derive? body
    let splice ← SourceSplice.derive? frame 0
    let source ← SourceResolve.resolve? splice symbols 1000
    pure (WriteAllLoopSource.select? source).isSome

def authored := Grass.Tests.Assembly.SourceResolve.authored

def replaceChars (needle replacement : List Char) : Nat → List Char → List Char
  | 0, text => text
  | fuel + 1, text =>
      if needle.isPrefixOf text then replacement ++ replaceChars needle replacement fuel (text.drop needle.length)
      else match text with
        | [] => []
        | char :: rest => char :: replaceChars needle replacement fuel rest

def mutated (needle replacement : String) : List Char :=
  replaceChars needle.toList replacement.toList authored.length authored

example : selected authored = some true := by decide +kernel

/-- A globally renamed loop may still parse, but is not the authored head. -/
example : selected (mutated "write_head" "other_head") = some false := by
  decide +kernel

/-- A changed invariant annotation is not silently accepted. -/
example : selected (mutated "write_all_loop(payload)" "other_loop(payload)") = some false := by
  decide +kernel

/-- Valid x86 bytes for a different ADD source cannot stand in for the actual
RAX count update named by the loop proof. -/
example : selected (mutated "add r13, rax" "add r13, rcx") = some false := by
  decide +kernel

end Grass.Tests.Console.WriteAllHead
