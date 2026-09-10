import Grass.ISA.X86.Execution.CallNormal
import Tests.Op.FakeIsa

namespace Grass.Tests.ExecutionCall

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical Grass.ISA.X86
  Grass.ISA.X86.Execution
open Grass.Tests.FakeIsa

private def stores : FreshSupply StorageTag := .initial
private def codeBacking := stores.fresh.1
private def iatBacking := stores.fresh.2.fresh.1
private def stackBacking := stores.fresh.2.fresh.2.fresh.1

private def record (backing : StorageId) (source : AllocationSourceId)
    (permission : Permission) (base : Nat) : AllocationRecord :=
  { extent := ⟨0, 64⟩, epoch := epoch₀, space := .cpuVirtual, source := source
    owners := [thread₀], permission := permission, live := true, backing := backing
    origin := 0, base := some base }

private def memory : MemoryState :=
  let code := ByteStore.empty.write 0 [0xFF, 0x15, 0xFA, 0x1F, 0, 0] true
  let iat := ByteStore.empty.write 0 (le64 0x5000) true
  let stack := ByteStore.empty.write 0 (List.replicate 64 0) true
  let m0 := (MemoryState.empty.installBacking? codeBacking ⟨64, code⟩).getD .empty
  let m1 := (m0.installBacking? iatBacking ⟨64, iat⟩).getD .empty
  let m2 := (m1.installBacking? stackBacking ⟨64, stack⟩).getD .empty
  (m2.allocateAll?
    [(bufferAlloc, record codeBacking .virtualAlloc .readExecute 0x1000),
     (viewAlloc, record iatBacking .mappedFile .readOnly 0x3000),
     (chainedAlloc, record stackBacking .mappedFile .readWrite 0x4000)]).getD .empty

private def initial : MachineState := .initial memory
private def before : State :=
  { machine := initial, gpr := fun r => if r = .rsp then 0x4040 else 0xCAFE
    rip := 0x1000, rflags := 0x10602 }

private def fetchD := acc bufferProv ⟨0, 6⟩ 0x1000 .execute .readExecute true false
private def readD := acc viewProv ⟨0, 8⟩ 0x3000 .read .readOnly true false
private def stackProv : Provenance := chainedProv
private def storeD := acc stackProv ⟨56, 8⟩ 0x4038 .write .readWrite false true

private def readPolicy : StepPolicy :=
  { policy with oracle := Oracle.ofMemory (fun _ _ => []) (fun _ _ _ => 0) }
private def noWrite : MachineState → AccessDescriptor → ByteSeq := fun _ _ => []
private def zeroByte : MachineState → (d : AccessDescriptor) → Nat → Byte := fun _ _ _ => 0
private def storeData : MachineState → AccessDescriptor → ByteSeq :=
  fun _ _ => le64 (BitVec.ofNat 64 0x1006)
private def storePolicy : StepPolicy :=
  { readPolicy with oracle := Oracle.ofMemory storeData (fun _ _ _ => 0) }

private inductive Operation where | fetch | read | store
private instance : HasOperationFacets Operation where
  facets
    | .fetch => { memoryEffects := some (.single fetchD), faults := some [.pageFault]
                  restartability := some .restartable, ordering := some .plain }
    | .read => { memoryEffects := some (.single readD), faults := some [.pageFault]
                 restartability := some .restartable, ordering := some .plain }
    | .store => { memoryEffects := some (.single storeD), faults := some [.pageFault]
                  restartability := some .restartable, ordering := some .plain }

private def cause : EventCause := ⟨⟨"call.normal"⟩⟩
private def stepF := step readPolicy initial (SomeOperation.of Operation.fetch)
  thread₀ .thread cause
private def afterF := match stepF with | .ran s => s | .rejected _ => initial
private def reachedF := initial.noteContext thread₀ .thread
private def resolvedF : reachedF.memory.ResolvedAccess fetchD.provenance fetchD.range :=
  (prepareAccess reachedF.memory fetchD).toOption.get (by decide)
private def completeF : CompleteCommitted fetchD :=
  (readPolicy.oracle.answerResolved reachedF fetchD resolvedF).get (by decide)
private def observedF := observedBytes resolvedF (fun _ => 0)
private def site : DecodedSite before.rip observedF :=
  (DecodedSite.check before.rip observedF).toOption.get (by decide)
private def fetch : FetchedSite before afterF := by
  let run : AccessRun initial afterF fetchD :=
    { policy := readPolicy, operation := SomeOperation.of Operation.fetch
      context := thread₀, contextKind := .thread, cause := cause, faultAt := fun _ => .none
      sequence := .single fetchD, selected := by rfl, substeps_exact := by rfl
      noFault := by rfl, ran := by rfl, resolved := resolvedF, prepared := by rfl
      complete := completeF, answerResolved := by simp [completeF, reachedF]
      clean := by decide }
  exact
    { descriptor := fetchD
      run := run
      writeData := noWrite
      indeterminate := zeroByte
      memoryOracle := by rfl
      intent := by rfl
      initialization := by rfl
      ledgerEffect := by rfl
      authorityEffect := by rfl
      address := by rfl
      placed := ⟨0x1000, by rfl⟩
      site := site
      noTrailing := by decide }

private def stepR := step readPolicy afterF (SomeOperation.of Operation.read)
  thread₀ .thread cause
private def afterR := match stepR with | .ran s => s | .rejected _ => afterF
private def reachedR := afterF.noteContext thread₀ .thread
private def resolvedR : reachedR.memory.ResolvedAccess readD.provenance readD.range :=
  (prepareAccess reachedR.memory readD).toOption.get (by decide)
private def completeR : CompleteCommitted readD :=
  (readPolicy.oracle.answerResolved reachedR readD resolvedR).get (by decide)
private def runR : AccessRun afterF afterR readD :=
  { policy := readPolicy, operation := SomeOperation.of Operation.read, context := thread₀
    contextKind := .thread, cause := cause, faultAt := fun _ => .none
    sequence := .single readD, selected := by rfl, substeps_exact := by rfl
    noFault := by rfl, ran := by rfl, resolved := resolvedR, prepared := by rfl
    complete := completeR, answerResolved := by simp [completeR, reachedR], clean := by decide }
private def read : ReadValue64 runR :=
  { writeData := fun _ _ => [], indeterminate := fun _ _ _ => 0
    memoryOracle := by rfl, reads := by rfl, writes := by rfl, width := by rfl
    initialization := by rfl }

private def stepS := step storePolicy afterR (SomeOperation.of Operation.store)
  thread₀ .thread cause
private def afterS := match stepS with | .ran s => s | .rejected _ => afterR
private def reachedS := afterR.noteContext thread₀ .thread
private def resolvedS : reachedS.memory.ResolvedAccess storeD.provenance storeD.range :=
  (prepareAccess reachedS.memory storeD).toOption.get (by decide)
private def completeS : CompleteCommitted storeD :=
  (storePolicy.oracle.answerResolved reachedS storeD resolvedS).get (by decide)
private def runS : AccessRun afterR afterS storeD :=
  { policy := storePolicy, operation := SomeOperation.of Operation.store, context := thread₀
    contextKind := .thread, cause := cause, faultAt := fun _ => .none
    sequence := .single storeD, selected := by rfl, substeps_exact := by rfl
    noFault := by rfl, ran := by rfl, resolved := resolvedS, prepared := by rfl
    complete := completeS, answerResolved := by simp [completeS, reachedS], clean := by decide }

private def receipt : CallNormal before afterF afterR afterS 0x1FFA :=
  { fetch := fetch, encoding := by decide, readDescriptor := readD, readRun := runR
    read := read, readPolicy := by rfl, readContext := by rfl, readContextKind := by rfl
    readCause := by rfl, fetchContext := by rfl, fetchSpace := by rfl
    readDescriptorContext := by rfl, readIntent := by rfl, readSpace := by rfl
    readOrdering := by rfl, readLedgerEffect := by rfl, readAuthorityEffect := by rfl
    readAddress := by decide, readPlaced := ⟨0x3000, by rfl⟩
    storeDescriptor := storeD, storeRun := runS, storePolicy := by rfl
    storeContext := by rfl, storeContextKind := by rfl, storeCause := by rfl
    storeDescriptorContext := by rfl, storeOracle := by rfl, storeIntent := by rfl
    storeSpace := by rfl, storeInitialization := by rfl, storeOrdering := by rfl
    storeWidth := by rfl, storeInitialized := by rfl, storeLedgerEffect := by rfl
    storeAuthorityEffect := by rfl, stackNoUnderflow := by decide
    storeAddress := by rfl, storePlaced := ⟨0x4000, by rfl⟩ }

example : receipt.result.rip = 0x5000 := by decide
example : receipt.result.gpr .rsp = 0x4038 := by decide
example : List.ofFn (fun i : Fin 8 => afterS.memory.cellAt? chainedAlloc (56 + i)) =
    (le64 (BitVec.ofNat 64 0x1006)).map (fun byte => some (byte, true)) := by decide
example : afterS.events.length = 3 := by decide
example : (0x4000 : MachineAddress).toNat + receipt.storeDescriptor.range.stop =
    (before.gpr .rsp).toNat := receipt.store_stop_toNat 0x4000 (by rfl)
example : addressOf 0x4000 receipt.storeDescriptor.range.stop = before.gpr .rsp :=
  receipt.store_stop_address 0x4000 (by rfl)
example : ∃ fetched target saved,
    receipt.result.machine.events = before.machine.events ++ [fetched, target, saved] := by
  obtain ⟨fetched, target, saved, events, _, _, _⟩ := receipt.events_exact
  exact ⟨fetched, target, saved, events⟩

example (mutated : CallNormal before afterF afterR afterS 0x1FFA)
    (wrong : mutated.readDescriptor.intent = .execute) : False := by
  rw [mutated.readIntent] at wrong
  contradiction

end Grass.Tests.ExecutionCall
