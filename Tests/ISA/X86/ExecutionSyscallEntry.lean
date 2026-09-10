import Grass.ISA.X86.Execution.SyscallEntry
import Tests.Op.FakeIsa

namespace Grass.Tests.ISA.X86.ExecutionSyscallEntry
open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def backing : StorageId := (FreshSupply.initial : FreshSupply StorageTag).fresh.1
private def memory : MemoryState :=
  let store := ByteStore.empty.write 0 SyscallEncoding.encoding.toBytes true
  let record : AllocationRecord :=
    { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual
      source := .virtualAlloc, owners := [thread₀], permission := .readExecute
      live := true, backing := backing, origin := 0, base := some 0x1000 }
  let backed := (MemoryState.empty.installBacking? backing ⟨64, store⟩).getD .empty
  (backed.allocateAll? [(bufferAlloc, record)]).getD .empty
private def before : State :=
  { machine := .initial memory
    gpr := fun r => if r = .rax then 0x1234567800000001 else
      if r = .rsp then 0x4000 else 0xDEADBEEF
    rip := 0x1000, rflags := 0x602 }
private def cpu : CpuAccessPolicy :=
  { operationPolicy := policy, context := thread₀, contextKind := .thread
    cause := ⟨⟨"syscall.entry"⟩⟩, code := bufferProv, stack := bufferProv
    faults := fun _ => [.pageFault] }
private def config : SyscallEntry.Configuration :=
  { longMode := true, code64 := true, enabled := true, fred := false
    callerShadowStack := false, kernelShadowStack := false, kernelIbt := false
    linearMode := .bits48, lstar := 0xFFFF800000001000
    star := 0x0023000800000000, flagsMask := 0x600 }
private def success := (SyscallEntry.enter cpu config before).toOption.get (by decide)

example : success.receipt.result.rip = config.lstar := success.receipt.rip_exact
example : success.receipt.result.gpr .rcx = 0x1002 := by decide
example : success.receipt.result.gpr .r11 = 0x602 := by decide
example : success.receipt.result.rflags = 2 := by decide
example : success.receipt.result.gpr .rax = 0x1234567800000001 := by decide
example : success.receipt.result.gpr .rsp = before.gpr .rsp := success.receipt.rsp_exact
example : success.receipt.controlProjection.cs = 8 := by decide
example : success.receipt.controlProjection.ss = 16 := by decide
example : success.afterEntry.events.length = 1 := by decide
example : success.receipt.result.machine.memory = before.machine.memory :=
  success.receipt.memory_frame

private def rejectsAtFetch (settings : SyscallEntry.Configuration) (state : State) : Bool :=
  match SyscallEntry.enter cpu settings state with
  | .error (.outsideProfile reached) =>
      reached.machine.events.length == 1 && reached.rip == state.rip &&
      reached.gpr .rcx == state.gpr .rcx && reached.rflags == state.rflags
  | _ => false

example : rejectsAtFetch { config with enabled := false } before = true := by decide
example : rejectsAtFetch { config with fred := true } before = true := by decide
example : rejectsAtFetch { config with callerShadowStack := true } before = true := by decide
example : rejectsAtFetch { config with kernelShadowStack := true } before = true := by decide
example : rejectsAtFetch { config with kernelIbt := true } before = true := by decide
example : rejectsAtFetch { config with lstar := 0x0000800000000000 } before = true := by decide
example : rejectsAtFetch config { before with rflags := 0x10602 } = true := by decide
example : rejectsAtFetch { config with star := 0x0000000B00000000 } before = true := by decide

end Grass.Tests.ISA.X86.ExecutionSyscallEntry
