import Grass.Refinement.Console.WriteAllFactory
import Grass.Refinement.Console.WriteFileLoad

namespace Grass.Tests.Console.WriteAllFactory

open Grass.Assembly Grass.ISA.X86 Grass.ISA.X86.Execution
open Grass.Memory Grass.Std.Logical Grass.Std.Console
open Grass.Platform.Win32.WriteFile Grass.Refinement.Console.WriteFileLoad
open Grass.Refinement.Console.WriteAllX86 Grass.Refinement.Console.WriteAllFactory
open BodyComputationFactory

/-- The actual initialized load supplies the full-RAX premise for the checked
factory suffix. The conclusion is about the factory's own final state. -/
example {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch afterLoad : MachineState}
    (load : FrameMemoryExecution.LoadNormal source before afterFetch afterLoad)
    (checks : CountChecks load.result) {policy : CpuAccessPolicy}
    (add : ArithmeticSuccess policy checks.result)
    (subtract : ArithmeticSuccess policy add.result)
    (jump : BranchSuccess policy subtract.result)
    (addSelected : add.instruction = .add .w64 .r13 .rax)
    (subSelected : subtract.instruction = .sub .w32 .r14 .rax)
    (displacement : BitVec 32)
    (jumpSelected : jump.instruction = .jump displacement)
    (argument : Argument) (value : BitVec 32)
    (observed : DwordAt before.machine.memory argument value)
    (provenance : load.access.descriptor.provenance = argument.provenance)
    (range : load.access.descriptor.range = argument.range)
    (destination : load.selection.result.destination = .rax)
    {payload : Vec Byte} {base : Nat} {cursor : WriteCursor payload}
    (placed : CursorRegisters payload base cursor checks.result)
    (count : WriteCount cursor) (accepted : value.toNat = count.value) :
    CursorRegisters payload base (advance cursor count) jump.result := by
  have loaded := (checked_load_value load checks argument value observed provenance range
    destination).trans accepted
  have advanced := (update add subtract jump addSelected subSelected displacement
    jumpSelected).cursor_advanced placed count loaded
  rwa [update_result] at advanced

end Grass.Tests.Console.WriteAllFactory
