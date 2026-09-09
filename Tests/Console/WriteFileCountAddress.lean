import Grass.Refinement.Console.WriteFileCountAddress
import Tests.Assembly.FrameLea

namespace Grass.Tests.Console.WriteFileCountAddress

open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Memory Grass.Platform.Win32 Grass.Platform.Win32.WriteFile
open Grass.Refinement.Console.WriteFileCountAddress

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def sameSlot? (chars : List Char) : Option Bool := do
  let body ← (SourceInput.extractHelloSourceChars chars).toOption
  let frame ← SourceFrame.derive? body
  match frame.program.collected.code.filterMap (FrameLea.resolve? frame 0),
      frame.program.collected.code.filterMap (FrameLoad.resolve? frame 0) with
  | [lea], [load] => pure (lea.destination == .r9 && load.destination == .rax &&
      lea.slot == load.slot && lea.address.range == load.address.range)
  | _, _ => none

example : sameSlot? Grass.Tests.Assembly.FrameLea.authored = some true := by decide +kernel

/-- Two valid DWORD slots cannot be substituted merely because both fit the
frame. Both operations resolve, but they identify different locals. -/
example : sameSlot? (Grass.Tests.Assembly.FrameLea.sample
    Grass.Tests.Assembly.FrameLea.twoLocals
    (source_chars "lea r9, second.addr\nmov eax, first")) = some false := by decide +kernel

example : sameSlot? (Grass.Tests.Assembly.FrameLea.sample
    Grass.Tests.Assembly.FrameLea.twoLocals
    (source_chars "lea r9, second.addr\nmov eax, second")) = some true := by decide +kernel

/-- Compose the actual source-selected LEA with the later source load. The
argument range and selected stack provenance come from the producer. -/
example {image : Loader.ImageInput} {inputs : Loader.EntryInputs}
    {loaded : Loader.LoadedImage image inputs} {policy loadPolicy : CpuAccessPolicy}
    {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before loadBefore : State}
    (lea : SourceLea policy source before) (selected : Cpu.policy? loaded before = some policy)
    (loadSelected : Cpu.policy? loaded loadBefore = some loadPolicy)
    (load : SourceResolve.LoadSelection source)
    (sameSlot : lea.resolved.slot = load.result.slot)
    (spatial : Resolved before.machine.memory lea.argument)
    (rsp : before.gpr .rsp = addressOf spatial.base lea.resolved.address.rootOffset) :
    lea.success.result.gpr lea.resolved.destination = addressOf spatial.base load.result.address.range.start ∧
    loadPolicy.stack = lea.argument.provenance := by
  refine ⟨?_, lea.load_stack_same selected loadSelected⟩
  rw [← lea.load_range_same load sameSlot]
  exact lea.argument_address spatial.base rsp

end Grass.Tests.Console.WriteFileCountAddress
