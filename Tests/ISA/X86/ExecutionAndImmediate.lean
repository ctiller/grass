import Grass.ISA.X86.Execution.BodyComputationFactory
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionAndImmediate

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def instruction : ArithmeticInstruction :=
  .andImmediate .w32 .rdx (.i32 0x0000FFFF)
private def bytes := instruction.encoding.toBytes
private def backing : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def memory : MemoryState :=
  let store := ByteStore.empty.write 0 bytes true
  let record : AllocationRecord :=
    { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
      source := .virtualAlloc, owners := [thread₀], permission := .readExecute
      live := true, backing := backing, origin := 0, base := some 0x1000 }
  let backed := (MemoryState.empty.installBacking? backing ⟨64, store⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty
private def before : State :=
  { machine := .initial memory
    gpr := fun r => if r = .rdx then 0xFFFF000000000003 else 0
    rip := 0x1000, rflags := 0x10603 }
private def cpu : CpuAccessPolicy :=
  { operationPolicy := policy, context := thread₀, contextKind := .thread
    cause := ⟨⟨"and.immediate"⟩⟩, code := bufferProv, stack := bufferProv
    faults := fun _ => [.pageFault] }
private def flags0 : RegisterSemantics.Flags Bool :=
  (instruction.effect before).flags.map (Option.getD · false)
private def flags1 : RegisterSemantics.Flags Bool := { flags0 with af := true }
private def result0 := BodyComputationFactory.arithmetic cpu before flags0
private def result1 := BodyComputationFactory.arithmetic cpu before flags1
private def success0 := result0.toOption.get (by decide)
private def success1 := result1.toOption.get (by decide)

example : (ArithmeticInstruction.select instruction.encoding).map (·.instruction) =
    some instruction := by decide
example : success0.result.gpr .rdx = 3 := by decide
example : BitVec.extractLsb' 32 32 (success0.result.gpr .rdx) = 0 := by decide
example : success0.result.statusFlags.cf = false := by decide
example : success0.result.statusFlags.of = false := by decide
example : success0.result.statusFlags.af = false := by decide
example : success1.result.statusFlags.af = true := by decide
example : success0.afterCompute.events.length = 1 := by decide

private def wrong : RegisterSemantics.Flags Bool := { flags0 with cf := true }
private def rejected : Bool := match BodyComputationFactory.arithmetic cpu before wrong with
  | .error (.flagsRejected reached (.andImmediate .w32 .rdx (.i32 0x0000FFFF))) =>
      reached.machine.events.length = 1
  | _ => false
example : rejected = true := by decide

end Grass.Tests.ISA.X86.ExecutionAndImmediate
