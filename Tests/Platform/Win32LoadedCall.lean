import Grass.Platform.Win32.Target

/-!
# Win32 loaded-indirect-call integration cases

These executable cases cross the x86 loaded-call boundary and the Win32
decoder.  Each call begins as encoded `call qword ptr [rip+disp32]` bytes;
the CPU loads the slot, pushes the architectural fallthrough address, and only
then offers an external call when that loaded target is in the selected
external-target set.  The tests deliberately keep the loader binding and the
IAT bytes separate, since agreement is checked from the observed call rather
than assumed from a symbol name.

They require the x86 loaded-call surface: `CallTarget.indirect`,
`State.externalTargets`, and the pending-fault resume path.  This file is kept
with the platform regressions because it checks their connection to Win32
bindings; the ISA's own byte-level cases live in `Tests/ISA/X86/SeamMemory`.
-/

namespace Grass.Tests.Win32LoadedCall

open Grass.ISA.X86
open Grass.ISA.X86.Target
open Grass.Platform.Win32.Target
open Grass.Target (StepOutcome)

def codeBase : Nat := 0x100
def iatSlot : Nat := 0x200
def stackTop : UInt64 := 0x400
def returnSlot : Nat := 0x3f8
def getStdTarget : UInt64 := 0x700
def writeFileTarget : UInt64 := 0x710

def region (base size : Nat) (readable writable executable : Bool) : Region :=
  { base := base, size := size, readable := readable, writable := writable,
    executable := executable }

def regs (updates : List (Gpr × UInt64)) : Gpr → UInt64 :=
  fun r => (updates.lookup r).getD 0

/-- A loaded image with one encoded call, ordinary data regions, and the
selected external target identities.  The caller supplies IAT and data bytes
separately so a test cannot accidentally turn a binding into an IAT fact. -/
def callState (instr : Instr) (registers : Gpr → UInt64)
    (externalTargets : List UInt64) (extra : List Region)
    (writes : List (Nat × List UInt8)) : State :=
  let code := encode instr
  let blank : State :=
    { reg := registers, rip := codeBase, mem := fun _ => none,
      regions := region codeBase code.length true false true :: extra,
      externalTargets := externalTargets, pendingFault := none }
  let loaded := blank.writeBytes codeBase code
  writes.foldl (fun (s : State) w => s.writeBytes w.1 w.2) loaded

def getStdBinding : ResolvedImport :=
  { importSymbol :=
      { library := "KERNEL32.dll", symbol := "GetStdHandle", slotAddress := iatSlot }
    targetAddress := getStdTarget }

def writeFileBinding : ResolvedImport :=
  { importSymbol :=
      { library := "KERNEL32.dll", symbol := "WriteFile", slotAddress := iatSlot }
    targetAddress := writeFileTarget }

def writeRequest : domain.Request := consoleRequest (.write .stdout [0x41, 0x42, 0x43])

def isStdoutQuery : Option domain.Request → Bool
  | some (.inl (.inl (.inl (.query .stdout)))) => true
  | _ => false

def isExpectedWrite : Option domain.Request → Bool
  | some (.inl (.inl (.inl (.write .stdout bytes)))) => bytes == [0x41, 0x42, 0x43]
  | _ => false

/-- The platform's explicit entry pointer reaches the CPU without changing
the top of the reserved stack mapping. -/
def initialUsesWin64EntryPointer : Bool :=
  let config : StackConfig Unit :=
    { stackTop := fun _ => 0x400, stackBytes := fun _ => 0x100 }
  let context := entry config [getStdBinding] ()
  let program : Grass.Target.Sectioned :=
    { sections := [], entry := codeBase, imports := [], stackBytes := 0x100 }
  let state := initial program context
  context.stackTop == 0x400 && state.reg .rsp == 0x3f8 &&
    state.externalTargets == [getStdTarget] &&
    (state.regionAt 0x3ff).isSome && (state.regionAt 0x400).isNone

/-- A matching loaded GetStdHandle target becomes external only after the
actual push.  The call snapshot sees both the post-push RSP and saved
fallthrough bytes. -/
def getStdAfterPushDecodes : Bool :=
  let instr := Instr.callRip 0xFA
  let before := callState instr
    (regs [(.rsp, stackTop), (.rcx, 0xFFFFFFF5)]) [getStdTarget]
    [region iatSlot 8 true false false, region returnSlot 8 true true false]
    [(iatSlot, toLE .w64 getStdTarget)]
  match step before with
  | .external call _ =>
      call.target == .indirect iatSlot getStdTarget &&
      call.rsp == UInt64.ofNat returnSlot &&
      call.returnAddress == UInt64.ofNat (codeBase + (encode instr).length) &&
      call.read returnSlot 8 == some (toLE .w64 (UInt64.ofNat (codeBase + (encode instr).length))) &&
      isStdoutQuery (decode [getStdBinding] call)
  | _ => false

/-- Replacing the IAT contents with a target outside the selected loaded
external target set makes the `call` an ordinary internal transfer.  A named
binding for the slot does not itself authorize interception. -/
def overwrittenIatIsInternal : Bool :=
  let instr := Instr.callRip 0xFA
  let unrelated : UInt64 := getStdTarget + 1
  let before := callState instr (regs [(.rsp, stackTop), (.rcx, 0xFFFFFFF5)]) [getStdTarget]
    [region iatSlot 8 true false false, region returnSlot 8 true true false]
    [(iatSlot, toLE .w64 unrelated)]
  match step before with
  | .internal after =>
      after.rip == unrelated.toNat && after.reg .rsp == UInt64.ofNat returnSlot &&
      after.readBytes returnSlot 8 == some
        (toLE .w64 (UInt64.ofNat (codeBase + (encode instr).length)))
  | _ => false

/-- The target load happens before the stack push even when the import slot
aliases the return cell.  The resulting call retains the pre-push target,
while the physical slot contains the saved fallthrough address. -/
def aliasedSlotRetainsPrePushTarget : Bool :=
  let instr := Instr.callRip 0x2F2
  let before := callState instr (regs [(.rsp, stackTop), (.rcx, 0xFFFFFFF5)]) [getStdTarget]
    [region returnSlot 8 true true false]
    [(returnSlot, toLE .w64 getStdTarget)]
  match step before with
  | .external call _ =>
      call.target == .indirect returnSlot getStdTarget &&
      call.read returnSlot 8 == some
        (toLE .w64 (UInt64.ofNat (codeBase + (encode instr).length))) &&
      isStdoutQuery (decode [{ getStdBinding with importSymbol :=
        { getStdBinding.importSymbol with slotAddress := returnSlot } }] call)
  | _ => false

/-- A WriteFile count slot can alias the saved return cell.  `encodeReturn`
writes the accepted DWORD before the x86 resume pops, so control follows the
live overwritten bytes rather than the original call fallthrough. -/
def writeFileCountAliasChangesResumeRip : Bool :=
  let instr := Instr.callRip 0xFA
  let before := callState instr
    (regs [(.rsp, stackTop), (.rcx, Handles.value .stdout), (.rdx, 0x300),
      (.r8, 3), (.r9, UInt64.ofNat returnSlot)]) [writeFileTarget]
    [region iatSlot 8 true false false, region 0x300 3 true false false,
      region returnSlot 48 true true false]
    [(iatSlot, toLE .w64 writeFileTarget), (0x300, [0x41, 0x42, 0x43]), (0x420, toLE .w64 0)]
  match step before with
  | .external call resume =>
      let after := resume (encodeReturn call writeRequest (.accepted 3))
      call.target == .indirect iatSlot writeFileTarget &&
      isExpectedWrite (decode [writeFileBinding] call) &&
      after.reg .rax == 1 && after.reg .rsp == stackTop && after.rip == 3
  | _ => false

/-- Effects of a native answer occur before its saved-return pop.  Releasing
the stack makes that pop a pending read fault; the next CPU step reports it,
without rolling back the already-applied register and memory effects. -/
def unmappingStackDefersReadFault : Bool :=
  let instr := Instr.callRip 0xFA
  let before := callState instr (regs [(.rsp, stackTop)]) [getStdTarget]
    [region iatSlot 8 true false false, region 0x300 1 true true false,
      region returnSlot 8 true true false]
    [(iatSlot, toLE .w64 getStdTarget)]
  match step before with
  | .external _ resume =>
      let returned : NativeReturn :=
        { rax := 0x55, rdx := none, writes := [(0x300, [0xAB])], clobbers := [],
          unmaps := [returnSlot] }
      let after := resume returned
      after.reg .rax == 0x55 && after.readBytes 0x300 1 == some [0xAB] &&
      (after.regionAt returnSlot).isNone &&
      match step after with
      | .fault (.readOutsideImage address) => address == returnSlot
      | _ => false
  | _ => false

def expect (label : String) (passed : Bool) : IO Unit :=
  unless passed do
    throw (IO.userError ("Win32 loaded-call integration failed: " ++ label))

def run : IO Unit := do
  expect "Win64 entry pointer preserves the reservation top" initialUsesWin64EntryPointer
  expect "GetStdHandle is captured after the architectural push" getStdAfterPushDecodes
  expect "overwritten IAT target remains an internal transfer" overwrittenIatIsInternal
  expect "aliased IAT slot retains the pre-push target snapshot" aliasedSlotRetainsPrePushTarget
  expect "WriteFile count alias changes resumed RIP" writeFileCountAliasChangesResumeRip
  expect "unmapped return slot faults only at the next CPU step" unmappingStackDefersReadFault

#eval run

end Grass.Tests.Win32LoadedCall

def main : IO Unit := Grass.Tests.Win32LoadedCall.run
