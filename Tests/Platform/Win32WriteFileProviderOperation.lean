import Grass.ISA.X86.Bytes
import Grass.Platform.Win32.WriteFile
import Tests.Platform.Win32WriteFile

/-!
# Request-derived `WriteFile` provider operation fixture

This fixture supplies the provider's two declared memory accesses: it reads the
entire prepared source buffer and writes the returned DWORD count.  It does not
claim that the current lower memory checker accepts that cross-context count
write; consumers must still establish a clean committed step separately.
-/
namespace Grass.Tests.Win32WriteFileProviderOperation

open Grass.Core Grass.Memory Grass.Op Grass.Std.Logical
open Grass.Platform.Win32.WriteFile

/-- The exact little-endian DWORD written to the caller's count slot. -/
def countBytes (request : Request) : ByteSeq :=
  Grass.ISA.X86.le32 request.requested

/-- The provider's full read of the prepared source buffer. -/
def bufferRead {memory : MemoryState} {request : Request}
    (prepared : Prepared memory request) (agent : ContextId) : AccessDescriptor :=
  { context := agent
    address := .numeric (addressOf prepared.buffer.base request.buffer.range.start)
    space := .cpuVirtual
    provenance := request.buffer.provenance
    range := request.buffer.range
    intent := .read
    requiredPermission := .readOnly
    alignment := 1
    initialization := .allBytesInitialized
    producesInitialized := false
    admittedFaults := [.pageFault, .generalProtection] }

/-- The provider's exact DWORD write to the prepared count slot. -/
def countWrite {memory : MemoryState} {request : Request}
    (prepared : Prepared memory request) (agent : ContextId) : AccessDescriptor :=
  { context := agent
    address := .numeric (addressOf prepared.countSlot.base request.countSlot.range.start)
    space := .cpuVirtual
    provenance := request.countSlot.provenance
    range := request.countSlot.range
    intent := .write
    requiredPermission := .readWrite
    alignment := 4
    initialization := .readsNothing
    producesInitialized := true
    admittedFaults := [.pageFault, .generalProtection] }

/-- One provider operation retains both request-derived descriptors in order. -/
inductive Operation where
  | write (bufferRead countWrite : AccessDescriptor)

instance : HasOperationFacets Operation where
  facets
    | .write buffer count =>
        { memoryEffects := some
            { substeps := [.access buffer, .access count]
              onFault := .priorEffectsVisible }
          faults := some [.pageFault, .generalProtection]
          restartability := some .notRestartable
          ordering := some .plain }

/-- Package the full buffer read followed by the returned-count write. -/
def operation {memory : MemoryState} {request : Request}
    (prepared : Prepared memory request) (agent : ContextId) : SomeOperation :=
  SomeOperation.of (Operation.write (bufferRead prepared agent) (countWrite prepared agent))

/--
The policy uses authoritative backing reads and supplies write data only for the
exact prepared count descriptor.  The caller supplies every other policy field.
-/
def policy {memory : MemoryState} {request : Request}
    (base : StepPolicy) (prepared : Prepared memory request) (agent : ContextId) : StepPolicy :=
  { base with oracle := (Oracle.ofMemory
      (fun _ descriptor =>
        if descriptor = countWrite prepared agent then countBytes request else [])
      (fun _ _ _ => 0)) }

/-- A provider action whose identity, context, and policy are all explicit. -/
def action {memory : MemoryState} (base : StepPolicy)
    (record : CallProtocol.Pending Request) (prepared : Prepared memory record.request) : Action where
  policy := policy base prepared record.agent
  operation := operation prepared record.agent
  kind := .externalAgent
  cause := ⟨⟨"writefile.provider"⟩⟩
  faultAt := fun _ => .none

/-! ## Small concrete descriptor and count checks -/

open Grass.Tests.Win32WriteFile

example : (bufferRead prepared record.agent).provenance = request.buffer.provenance := rfl
example : (bufferRead prepared record.agent).range = request.buffer.range := rfl
example : (bufferRead prepared record.agent).address =
    .numeric (addressOf prepared.buffer.base request.buffer.range.start) := rfl
example : (countWrite prepared record.agent).provenance = request.countSlot.provenance := rfl
example : (countWrite prepared record.agent).range = request.countSlot.range := rfl
example : (countWrite prepared record.agent).address =
    .numeric (addressOf prepared.countSlot.base request.countSlot.range.start) := rfl
example : countBytes request = [3, 0, 0, 0] := by decide
example : (countBytes request).length = request.countSlot.range.size := by decide

/-- Reuse the actual initialized-count history from the existing denial
fixture. The ordinary checker must still reject the conflicting provider write. -/
def attemptedAction : Action := action zeroPolicy record prepared

def attempted := CallProtocol.step? afterZero attemptedAction.policy attemptedAction.operation
  record.agent attemptedAction.kind attemptedAction.cause attemptedAction.faultAt

private def check (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError "provider operation unexpectedly bypassed history conflict")

#eval check (match attempted with
  | none => false
  | some reached =>
      reached.machine.violations.records?.map (fun item => item.class_) == [.conflictingAccess])

end Grass.Tests.Win32WriteFileProviderOperation
