import Grass.ISA.X86.Execution.CheckedStep
import Tests.Op.FakeIsa

namespace Grass.Tests.CheckedStep

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa Grass.ISA.X86.Execution.CheckedExecution

private def mov := BasicInstructions.movRegReg .w64 .rax .rbx
private def add := BasicInstructions.addRegReg .w64 .rax .rbx
private def store := (movMem32Imm32 (.base .rsp 0x20) 0xAABBCCDD).get (by decide)
private def load := (BasicInstructions.movReg32Mem .rcx (.base .rsp 0x20)).get (by decide)
private def stop := BasicInstructions.ud2
private def codeBytes := mov.toBytes ++ add.toBytes ++ store.toBytes ++ load.toBytes ++ stop.toBytes

private def stores : FreshSupply StorageTag := .initial
private def codeBacking := stores.fresh.1
private def stackBacking := stores.fresh.2.fresh.1
private def record (backing : StorageId) (source : AllocationSourceId)
    (permission : Permission) (base : Nat) (extent : Nat) : AllocationRecord :=
  { extent := ⟨0, extent⟩, epoch := epoch₀, space := .cpuVirtual, source := source
    owners := [thread₀], permission := permission, live := true, backing := backing
    origin := 0, base := some base }
private def memoryFor (bytes : ByteSeq) : MemoryState :=
  let code := ByteStore.empty.write 0 bytes true
  let stack := ByteStore.empty.write 0 (List.replicate 64 0) true
  let m0 := (MemoryState.empty.installBacking? codeBacking ⟨64, code⟩).getD .empty
  let m1 := (m0.installBacking? stackBacking ⟨64, stack⟩).getD .empty
  (m1.allocateAll? [(bufferAlloc, record codeBacking .virtualAlloc .readExecute 0x1000 64),
    (chainedAlloc, record stackBacking .mappedFile .readWrite 0x4000 64)]).getD .empty
private def initial : State :=
  { machine := .initial (memoryFor codeBytes)
    gpr := fun r => if r = .rax then 99 else if r = .rbx then 2
      else if r = .rcx then 0xFFFF000000000001 else if r = .rsp then 0x4000 else 0
    rip := 0x1000, rflags := 0x10602 }
private def cpu : CpuAccessPolicy :=
  { operationPolicy := policy, context := thread₀, contextKind := .thread
    cause := ⟨⟨"checked.step"⟩⟩, code := bufferProv, stack := chainedProv
    faults := fun _ => [.pageFault] }
private def clear : RegisterSemantics.Flags Bool :=
  ⟨false, false, false, false, false, false⟩
private def wrong : RegisterSemantics.Flags Bool :=
  ⟨true, false, false, false, false, false⟩
private def advance (state : State) (flags := clear) : State :=
  match evaluate cpu state (.normal flags) with
  | some outcome => outcome.state
  | none => state
private def afterMov := advance initial
private def afterAdd := advance afterMov
private def afterStore := advance afterAdd
private def afterLoad := advance afterStore

example : codeBytes.length = mov.size + add.size + store.size + load.size + stop.size := by
  simp [codeBytes, InsnEncoding.size, Nat.add_assoc]
example : afterLoad.gpr .rax = 4 := by decide
example : afterLoad.gpr .rcx = 0xAABBCCDD := by decide
example : afterLoad.machine.memory.cellAt? chainedAlloc 32 = some (0xDD, true) := by decide
example : afterLoad.rip = BitVec.ofNat 64 (0x1000 + mov.size + add.size + store.size + load.size) := by decide
example : afterLoad.machine.events.length = 6 := by decide

private def stopped := evaluate cpu afterLoad (.normal clear)
private def stoppedExactly : Bool := match stopped with
  | some (.outsideProfile reached (.instruction encoding)) =>
      reached.machine.events.length = 7 && encoding == stop
  | _ => false
example : stoppedExactly = true := by decide

example : evaluate cpu afterMov (.normal wrong) = none := by decide

private def sub := (StackInstruction.subRsp (.i8 8)).encoding
private def beforeSub : State :=
  { machine := MachineState.initial (memoryFor (InsnEncoding.toBytes sub))
    gpr := fun r => if r = .rsp then 0x4038 else initial.gpr r
    rip := initial.rip, rflags := initial.rflags }
private def subFlags := completedSubStatus beforeSub (.i8 8)
private def afterSub := advance beforeSub subFlags
private def wrongSub : RegisterSemantics.Flags Bool :=
  { subFlags with cf := !subFlags.cf }
example : afterSub.gpr .rsp = 0x4030 := by decide
example : evaluate cpu beforeSub (.normal wrongSub) = none := by decide

private def explicitFault := evaluate cpu initial (.fault .pageFault)
private def faultRetainsPrefix : Bool := match explicitFault with
  | some (.outsideProfile reached (.faultTransfer .pageFault)) =>
      reached.rip == initial.rip && reached.machine.events.length = 0
  | _ => false
example : faultRetainsPrefix = true := by decide

end Grass.Tests.CheckedStep
