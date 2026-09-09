import Grass.ISA.X86.Execution.BodyComputationFactory
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.BodyComputationFactory

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def backing : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def makeMemory (bytes : ByteSeq) : MemoryState :=
  let store := ByteStore.empty.write 0 bytes true
  let record : AllocationRecord :=
    { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
      source := .virtualAlloc, owners := [thread₀], permission := .readExecute
      live := true, backing := backing, origin := 0, base := some 0x1000 }
  let backed := (MemoryState.empty.installBacking? backing ⟨64, store⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty

private def makeState (bytes : ByteSeq) (rflags : BitVec 64 := 0) : State :=
  { machine := .initial (makeMemory bytes)
    gpr := fun register => if register = .rax then 1 else if register = .rbx then 2 else 0
    rip := 0x1000
    rflags := rflags }

private def cpu : CpuAccessPolicy :=
  { operationPolicy := policy, context := thread₀, contextKind := .thread
    cause := ⟨⟨"body.factory"⟩⟩, code := bufferProv, stack := bufferProv
    faults := fun _ => [.pageFault] }

private def addState := makeState [0x48, 0x01, 0xC3]
private def addInstruction : ArithmeticInstruction := .add .w64 .rbx .rax
private def addFlags : RegisterSemantics.Flags Bool :=
  (addInstruction.effect addState).flags.map (Option.getD · false)
private def addResult := BodyComputationFactory.arithmetic cpu addState addFlags
private def addSuccess := addResult.toOption.get (by decide)
example : addSuccess.result.gpr .rbx = 3 := by decide
example : addSuccess.result.rip = 0x1003 := by decide
example : addSuccess.result.statusFlags = addFlags := addSuccess.status_exact
example : addSuccess.afterCompute.events.length = 1 := by decide

private def badFlags : RegisterSemantics.Flags Bool :=
  { addFlags with cf := !addFlags.cf }
private def badResult := BodyComputationFactory.arithmetic cpu addState badFlags
private def rejectedFlags : Bool := match badResult with
  | .error (.flagsRejected reached (.add .w64 .rbx .rax)) =>
      reached.machine.events.length = 1
  | _ => false
example : rejectedFlags = true := by decide

private def preservedRflags : BitVec 64 := 0x10600

private def testState := makeState [0x48, 0x85, 0xC3] preservedRflags
private def testInstruction : ArithmeticInstruction := .test .w64 .rbx .rax
private def testFlags0 : RegisterSemantics.Flags Bool :=
  (testInstruction.effect testState).flags.map (Option.getD · false)
private def testFlags1 : RegisterSemantics.Flags Bool := { testFlags0 with af := true }
private def testResult0 := BodyComputationFactory.arithmetic cpu testState testFlags0
private def testResult1 := BodyComputationFactory.arithmetic cpu testState testFlags1
private def testSuccess0 := testResult0.toOption.get (by decide)
private def testSuccess1 := testResult1.toOption.get (by decide)
example : testSuccess0.result.statusFlags.af = false := by decide
example : testSuccess1.result.statusFlags.af = true := by decide
example : testSuccess0.result.rflags &&& 0x10600 = 0x600 := by decide
example : testSuccess1.result.rflags &&& 0x10600 = 0x600 := by decide

private def xorState := makeState [0x48, 0x31, 0xC3] preservedRflags
private def xorInstruction : ArithmeticInstruction := .xor .w64 .rbx .rax
private def xorFlags0 : RegisterSemantics.Flags Bool :=
  (xorInstruction.effect xorState).flags.map (Option.getD · false)
private def xorFlags1 : RegisterSemantics.Flags Bool := { xorFlags0 with af := true }
private def xorResult0 := BodyComputationFactory.arithmetic cpu xorState xorFlags0
private def xorResult1 := BodyComputationFactory.arithmetic cpu xorState xorFlags1
private def xorSuccess0 := xorResult0.toOption.get (by decide)
private def xorSuccess1 := xorResult1.toOption.get (by decide)
example : xorSuccess0.result.statusFlags.af = false := by decide
example : xorSuccess1.result.statusFlags.af = true := by decide
example : xorSuccess0.result.rflags &&& 0x10600 = 0x600 := by decide
example : xorSuccess1.result.rflags &&& 0x10600 = 0x600 := by decide

private def branchState := makeState [0x0F, 0x84, 0x04, 0, 0, 0] 0x40
private def branchResult := BodyComputationFactory.branch cpu branchState
private def branchSuccess := branchResult.toOption.get (by decide)
example : branchSuccess.result.rip = 0x100A := by decide
example : branchSuccess.afterCompute.events.length = 1 := by decide

private def negativeBranch : InsnEncoding := Rel32.encode .equal 0xFFFFE000
private def takenNegativeState := makeState negativeBranch.toBytes 0x40
private def takenNegativeResult := BodyComputationFactory.branch cpu takenNegativeState
private def takenNegativeRejected : Bool := match takenNegativeResult with
  | .error (.targetOutOfRange reached (.equal 0xFFFFE000)) =>
      reached.machine.events.length = 1
  | _ => false
example : takenNegativeRejected = true := by decide

private def untakenNegativeState := makeState negativeBranch.toBytes 0
private def untakenNegativeResult := BodyComputationFactory.branch cpu untakenNegativeState
private def untakenNegativeSuccess := untakenNegativeResult.toOption.get (by decide)
example : untakenNegativeSuccess.result.rip = 0x1006 := by decide
example : untakenNegativeSuccess.afterCompute.events.length = 1 := by decide

private def leaEncoding : InsnEncoding :=
  (leaR64 .rcx (.ripRelative 0x20)).get (by decide)
private def leaState := makeState leaEncoding.toBytes
private def leaResult := BodyComputationFactory.lea cpu leaState
private def leaSuccess := leaResult.toOption.get (by decide)
example : leaSuccess.result.gpr .rcx = 0x1027 := by decide
example : leaSuccess.result.rip = 0x1007 := by decide
example : leaSuccess.afterCompute.events.length = 1 := by decide

end Grass.Tests.ISA.X86.BodyComputationFactory
