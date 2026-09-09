import Grass.Refinement.Console.WriteFileLoad

namespace Grass.Tests.Console.WriteFileLoad

open Grass.Assembly Grass.ISA.X86.Execution Grass.Memory Grass.Op Grass.Std.Logical Grass.Std.Console
open Grass.Platform.Win32.WriteFile Grass.Refinement.Console.WriteFileLoad
open Grass.Refinement.Console.WriteAllX86

/-- The numeric premise for the actual update is discharged by the actual
load/check chain, with no independent chosen RAX value. -/
example {frame : SourceFrame.Result} {rootOffset : Nat}
    {source : SourceResolve.Result frame rootOffset} {before : State}
    {afterFetch afterLoad : MachineState}
    (load : FrameMemoryExecution.LoadNormal source before afterFetch afterLoad)
    (checks : CountChecks load.result) (update : UpdateRun checks.result)
    (argument : Argument) (value : BitVec 32)
    (observed : DwordAt before.machine.memory argument value)
    (provenance : load.access.descriptor.provenance = argument.provenance)
    (range : load.access.descriptor.range = argument.range)
    (destination : load.selection.result.destination = .rax)
    {payload : Vec Byte} {base : Nat} {cursor : WriteCursor payload}
    (placed : CursorRegisters payload base cursor checks.result)
    (count : WriteCount cursor) (accepted : value.toNat = count.value) :
    CursorRegisters payload base (advance cursor count) update.result :=
  update.cursor_advanced placed count
    ((checked_load_value load checks argument value observed provenance range destination).trans accepted)

/-- Equal widths do not identify the actual accessed count slot. -/
example {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (_read : ReadValue32 run)
    (_argument : Argument) (_value : BitVec 32)
    (_observed : DwordAt before.memory _argument _value)
    (_provenance : descriptor.provenance = _argument.provenance)
    (_sameSize : descriptor.range.size = _argument.range.size) : True := by
  fail_if_success
    have _wrong := read_value _read _argument _value _observed _provenance _sameSize
  trivial

/-- A slot observation from unrelated memory cannot replace the actual
pre-read state, even with the same argument and DWORD value. -/
example {before after : MachineState} {descriptor : AccessDescriptor}
    {run : AccessRun before after descriptor} (_read : ReadValue32 run)
    (_argument : Argument) (_value : BitVec 32) (_other : MemoryState)
    (_observed : DwordAt _other _argument _value)
    (_provenance : descriptor.provenance = _argument.provenance)
    (_range : descriptor.range = _argument.range) : True := by
  fail_if_success
    have _wrong := read_value _read _argument _value _observed _provenance _range
  trivial

end Grass.Tests.Console.WriteFileLoad
