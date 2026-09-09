import Grass.Assembly.SourceStore
import Grass.Assembly.Store32Execution
import Tests.Assembly.SourceLiteral
import Tests.Memory.Spike1Policy

namespace Grass.Tests.Assembly.SourceStore

open Grass.Assembly Grass.Assembly.SourceInput Grass.Assembly.SourceStore
open Grass.ABI.Win64 Grass.ISA.X86
open Grass.Tests.Spike1 Grass.Tests.Spike1Policy Tests.Memory.Spike1Block

-- This file must be directly re-elaborated by check-source-input.ps1; Lake
-- does not register the authored file below as an imported-module dependency.
def authored : List Char := include_source_chars "../../Spikes/1_Hello_World/Program.lean"

def selectedStore? (body : Body) : Option SourceLine := do
  let slots ← uint32StackSlots body
  let candidates := body.lines.filter fun line => match line.parsed with
    | .symbolicStore destination _ => slots.contains destination
    | _ => false
  match candidates with
  | [line] => some line
  | _ => none

def fromChars? (source : List Char) (rspRootOffset : Nat := 0) : Option Store32.Resolved := do
  let body ← (extractHelloSourceChars source).toOption
  let slots ← uint32StackSlots body
  let line ← selectedStore? body
  let frame := frameForSlots spike1FrameLayout.argumentCount spike1SavedRegisters slots
  resolveLine? frame rspRootOffset body line

def executeChars? (source : List Char) : Option (Store32.Resolved × Grass.Memory.MachineState) := do
  let resolved ← fromChars? source frameBaseOffset
  if hrange : transferredWrite.range = resolved.range then do
    let final ← (Store32Execution.step policy machine₀ resolved transferredWrite
      hrange rfl .thread ⟨⟨"source-store32"⟩⟩).state?
    pure (resolved, final)
  else none

-- One kernel-checked connection from the actual authored occurrence through
-- parsing, slot placement, value resolution, the existing transition, and its
-- committed bytes/event. The fixture still supplies the machine/address setup.
def outcomeView (result : Store32.Resolved × Grass.Memory.MachineState) :
    String × List (BitVec 8) × Bool × Option (Option (List (BitVec 8))) ×
      List (Option (BitVec 8)) :=
  let (resolved, final) := result
  (resolved.input.slot, resolved.writeBytes, decide final.violations.IsEmpty,
    final.events.getLast?.map (fun event => event.event.valueWritten),
    (List.range resolved.writeBytes.length).map fun i =>
      final.memory.byteAt? stackAlloc (resolved.range.start + i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 512 in
example : (executeChars? authored).map outcomeView =
    some ("transferred", le32 0, true, some (some (le32 0)), (le32 0).map some) := by
  decide +kernel

-- Small adversarial inputs exercise the same parser and resolver; the theorem
-- above is the connection to the actual spike. Keep these cheap to recheck.
def sample (type body : List Char) : List Char :=
  (source_chars "def helloSource := withStack (value : ") ++ type ++
    (source_chars " := 0) asm_source {\n ") ++ body ++ (source_chars "\n}")

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (fromChars? (sample (source_chars "UInt32")
    (source_chars "mov value, 305419896"))).map Store32.Resolved.writeBytes =
    some (le32 305419896) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (fromChars? (sample (source_chars "UInt64") (source_chars "mov value, 0"))).isNone =
    true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : (fromChars? (sample (source_chars "UInt32")
    (source_chars "mov value, 4294967296"))).isNone = true := by decide

example : (fromChars? (sample (source_chars "UInt32")
    (source_chars "mov value, 0\n mov value, 1"))).isNone = true := by decide

end Grass.Tests.Assembly.SourceStore
