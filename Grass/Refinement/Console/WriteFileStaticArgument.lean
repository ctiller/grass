import Grass.Assembly.LoadedStaticArgument
import Grass.Platform.Win32.WriteFilePrepare
import Grass.Semantics.OutputCut

/-! Connect a checked source-static suffix to the existing WriteFile request.
The incoming register and ABI checks remain in `WriteFile.EntryFactory.prepare?`;
these adapters do not require an instruction sequence that computes the arguments.
-/

namespace Grass.Refinement.Console.WriteFileStaticArgument

open Grass.Assembly Grass.Memory Grass.Std.Logical Grass.Semantics
open Grass.Platform.Win32 Grass.Platform.Win32.Loader

variable {image : ImageInput} {inputs : EntryInputs}
  {table : StaticObjects.Table} {layout : StaticSection.Layout table} {sectionIndex : Nat}
  {binding : SourceStaticBindings.Binding image.plan layout sectionIndex}
  {loaded : LoadedImage image inputs} {offset : Nat}

/-- Use the existing request constructor with the producer's computed buffer and bytes. -/
def requestOf (state : Grass.ISA.X86.Execution.State)
    (prepared : LoadedStaticArgument.Prepared binding loaded state.machine.memory offset)
    (countSlot : CallMemory.Argument) : WriteFile.Request :=
  WriteFile.EntryFactory.requestOf state prepared.argument countSlot prepared.bytes

@[simp] theorem requestOf_buffer (state : Grass.ISA.X86.Execution.State)
    (prepared : LoadedStaticArgument.Prepared binding loaded state.machine.memory offset)
    (countSlot : CallMemory.Argument) :
    (requestOf state prepared countSlot).buffer = prepared.argument := rfl

@[simp] theorem requestOf_bytes (state : Grass.ISA.X86.Execution.State)
    (prepared : LoadedStaticArgument.Prepared binding loaded state.machine.memory offset)
    (countSlot : CallMemory.Argument) :
    (requestOf state prepared countSlot).bytes = prepared.bytes := rfl

/-- `requestOf_input` exposes the producer's initialized snapshot through the
existing WriteFile input predicate, at the same current machine. -/
theorem requestOf_input (state : Grass.ISA.X86.Execution.State)
    (prepared : LoadedStaticArgument.Prepared binding loaded state.machine.memory offset)
    (countSlot : CallMemory.Argument) :
    WriteFile.InputMatches state.machine.memory (requestOf state prepared countSlot) := by
  intro index
  exact prepared.cells (by
    simp [Vec.get?])

/-- The request bytes are the exact remaining output at the original object's cut. -/
theorem requestOf_bytes_remaining (state : Grass.ISA.X86.Execution.State)
    (cut : OutputCut binding.object.declaration.bytes)
    (prepared : LoadedStaticArgument.Prepared binding loaded state.machine.memory cut.offset)
    (countSlot : CallMemory.Argument) :
    (requestOf state prepared countSlot).bytes = cut.remaining :=
  prepared.bytesExact

end Grass.Refinement.Console.WriteFileStaticArgument
