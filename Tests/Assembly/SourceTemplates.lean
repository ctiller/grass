import Grass.Assembly.SourceTemplates
import Tests.Assembly.SourceLiteral

namespace Grass.Tests.Assembly.SourceTemplates

open Grass.Assembly Grass.Assembly.SourceTemplates
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def actual? : Option (SourceFrame.Result × List Nat) := do
  let body ← (SourceInput.extractHelloSourceChars authored).toOption
  let frame ← SourceFrame.derive? body
  let result ← derive? frame 0
  pure (frame, result.sizes)

def actualCandidateCounts : Option (List (Nat × Nat)) := do
  let body ← (SourceInput.extractHelloSourceChars authored).toOption
  let frame ← SourceFrame.derive? body
  pure (List.zipWith (fun item flow => (item.lineNumber, candidateCount frame 0 item flow))
    frame.program.collected.code frame.program.flows)

example : actual?.map (fun pair =>
    (pair.1.program.collected.code.length, pair.2.length)) = some (42, 42) := by
  decide +kernel

example : actualCandidateCounts.map (fun counts => counts.all fun pair => pair.2 = 1) = some true := by
  decide +kernel

-- A local named like a platform constant makes two resolvers succeed. The
-- classifier rejects the overlap instead of selecting whichever ran first.
def collision : List Char := source_chars
  "def helloSource : MachineSource plan := withStack (STD_OUTPUT_HANDLE : UInt32 := 0) withCallFrame WriteFile asm_source (statics := statics) {\nmov ecx, STD_OUTPUT_HANDLE\nud2\n}"

def collisionRejected : Bool :=
  match (SourceInput.extractHelloSourceChars collision).toOption with
  | none => false
  | some body => match SourceFrame.derive? body with
    | none => false
    | some frame => match frame.program.collected.code, frame.program.flows with
      | item :: _, flow :: _ => (classify? frame 0 item flow).isNone
      | _, _ => false

example : collisionRejected = true := by decide +kernel

def mismatchedFlowsRejected : Bool :=
  match (SourceInput.extractHelloSourceChars authored).toOption with
  | none => false
  | some body => match SourceFrame.derive? body with
    | none => false
    | some frame =>
      (classifyAll? frame 0 frame.program.collected.code []).isNone

example : mismatchedFlowsRejected = true := by decide +kernel

def unsupported : List Char := source_chars
  "def helloSource : MachineSource plan := withCallFrame WriteFile asm_source (statics := statics) {\nmov eax, UNKNOWN\nud2\n}"

def unsupportedRejected : Bool :=
  match (SourceInput.extractHelloSourceChars unsupported).toOption with
  | none => false
  | some body => match SourceFrame.derive? body with
    | none => false
    | some frame => (derive? frame 0).isNone

example : unsupportedRejected = true := by decide +kernel

end Grass.Tests.Assembly.SourceTemplates
