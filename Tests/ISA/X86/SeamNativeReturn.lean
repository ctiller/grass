import Tests.ISA.X86.SeamFixtures

namespace Grass.Tests.ISA.X86.SeamNativeReturn

open Grass.ISA.X86
open Grass.ISA.X86.Target
open Grass.Target (Sectioned StepOutcome)
open Grass.Tests.ISA.X86.SeamFixtures

def slot : Nat := 0x3F8
def target : UInt64 := 0x777
def fallthrough : UInt64 := 0x106

def callState (targets : List UInt64) (extra : List Region := []) : State :=
  { withBytes
      (blankState (.callRip 0x2F2) (regs [(.rsp, 0x400)])
        (region slot 8 true true false :: extra))
      [(slot, [0x77, 0x07, 0, 0, 0, 0, 0, 0])] with
    externalTargets := targets }

def capturedExternal? (s : State) : Option (NativeCall × (NativeReturn → State)) :=
  match step s with
  | .external call resume => some (call, resume)
  | _ => none

def configuredCaptureIsPostPush : Bool :=
  match capturedExternal? (callState [target]) with
  | some (call, _) => call.target = .indirect slot target &&
      call.rsp.toNat == slot && (call.reg .rsp).toNat == slot &&
      call.returnAddress == fallthrough &&
      call.read slot 8 = some [0x06, 0x01, 0, 0, 0, 0, 0, 0]
  | none => false

def unconfiguredTargetIsInternal : Bool :=
  match internal? (step (callState [])) with
  | some after => after.rip == target.toNat && (after.reg .rsp).toNat == slot &&
      after.readBytes slot 8 = some [0x06, 0x01, 0, 0, 0, 0, 0, 0]
  | none => false

def overwrittenKnownSlotIsInternal : Bool :=
  let s := withBytes (callState [target])
    [(slot, [0x88, 0x08, 0, 0, 0, 0, 0, 0])]
  match internal? (step s) with
  | some after => after.rip == 0x888 && (after.reg .rsp).toNat == slot
  | none => false

def returnWritesSavedSlotBeforePop : Bool :=
  match capturedExternal? (callState [target]) with
  | some (_, resume) =>
      let after := resume
        { rax := 0, rdx := none, writes := [(slot, [0x88, 0x08, 0, 0, 0, 0, 0, 0])]
          clobbers := [], maps := [], unmaps := [] }
      after.rip == 0x888 && (after.reg .rsp).toNat == 0x400 && after.pendingFault = none
  | none => false

def unmapThenPopRecordsExactFault : Bool :=
  match capturedExternal? (callState [target] [region 0x500 8 true true false]) with
  | some (_, resume) =>
      let after := resume
        { rax := 0xAA, rdx := none, writes := [(0x500, [1, 2, 3, 4])], clobbers := [],
          maps := [], unmaps := [slot] }
      after.pendingFault = some (.readOutsideImage slot) && (after.reg .rsp).toNat == slot &&
        after.reg .rax == 0xAA && after.readBytes slot 8 = none &&
        after.readBytes 0x500 4 = some [1, 2, 3, 4] &&
        (match step after with
        | .fault (.readOutsideImage address) => address == slot
        | _ => false)
  | none => false

def clobberedRspUsesActualPostReturnValue : Bool :=
  let s := withBytes (callState [target] [region 0 8 true false false])
    [(0, [0x99, 0x09, 0, 0, 0, 0, 0, 0])]
  match capturedExternal? s with
  | some (_, resume) =>
      let after := resume
        { rax := 0, rdx := none, writes := [], clobbers := [.rsp], maps := [], unmaps := [] }
      after.rip == 0x999 && (after.reg .rsp).toNat == 8 && after.pendingFault = none
  | none => false

def explicitReturnsWinOverClobbers : Bool :=
  match capturedExternal? (callState [target]) with
  | some (_, resume) =>
      let after := resume
        { rax := 0xAA, rdx := some 0xDD, writes := [], clobbers := [.rax, .rdx],
          maps := [], unmaps := [] }
      after.reg .rax == 0xAA && after.reg .rdx == 0xDD &&
        after.rip == fallthrough.toNat && (after.reg .rsp).toNat == 0x400 && after.pendingFault = none
  | none => false

def capturedSyscall? (s : State) : Option (NativeCall × (NativeReturn → State)) :=
  match step s with
  | .external call resume => some (call, resume)
  | _ => none

def syscallExplicitReturnsWinOverClobbers : Bool :=
  match capturedSyscall? (blankState .syscall (regs []) []) with
  | some (call, resume) =>
      let after := resume
        { rax := 0xAA, rdx := some 0xDD, writes := [], clobbers := [.rax, .rdx],
          maps := [], unmaps := [] }
      call.target = .syscall && after.reg .rax == 0xAA && after.reg .rdx == 0xDD
  | none => false

def syscallMapsBeforeWritesAndUnmapsLast : Bool :=
  let s := blankState .syscall (regs []) [region 0x500 4 true true false]
  match capturedSyscall? s with
  | some (_, resume) =>
      let after := resume
        { rax := 0, rdx := none, writes := [(0x600, [1, 2, 3, 4]), (0x700, [9])],
          clobbers := [],
          maps := [{ base := 0x600, size := 4, readable := true, writable := true },
            { base := 0x700, size := 1, readable := true, writable := true }],
          unmaps := [0x500, 0x700] }
      after.readBytes 0x600 4 = some [1, 2, 3, 4] && after.readBytes 0x500 1 = none &&
        after.readBytes 0x700 1 = none && after.regionAt 0x700 = none
  | none => false

def genericProgram : Sectioned :=
  { sections := [], entry := 0x100, imports := [], stackBytes := 0x40 }

def initialContext (entryRsp : Option UInt64) : InitialContext :=
  { reg := regs [], stackTop := 0x800, stackBytes := 0x40,
    argumentBlockAddress := 0x900, argumentBlock := [], initialStackPointer := entryRsp,
    externalTargets := [target] }

def initialStackPointerDefaultsToReservationTop : Bool :=
  let s := initial genericProgram (initialContext none)
  (s.reg .rsp).toNat == 0x800 && s.externalTargets == [target]

def initialStackPointerOverridePreservesReservation : Bool :=
  let s := initial genericProgram (initialContext (some 0x7D0))
  (s.reg .rsp).toNat == 0x7D0 && s.writableAt 0x7C0 && s.writableAt 0x7FF &&
    !s.writableAt 0x800

def run : IO Unit := do
  expect "external capture uses post-push call state" configuredCaptureIsPostPush
  expect "unconfigured indirect target stays internal" unconfiguredTargetIsInternal
  expect "overwritten known slot uses loaded target" overwrittenKnownSlotIsInternal
  expect "native return writes saved slot before pop" returnWritesSavedSlotBeforePop
  expect "unmap before pop records exact pending fault" unmapThenPopRecordsExactFault
  expect "clobbered rsp controls actual pop" clobberedRspUsesActualPostReturnValue
  expect "explicit rax and rdx win over clobbers" explicitReturnsWinOverClobbers
  expect "syscall explicit returns win over clobbers" syscallExplicitReturnsWinOverClobbers
  expect "syscall maps before writes and unmaps last" syscallMapsBeforeWritesAndUnmapsLast
  expect "initial rsp defaults to reservation top" initialStackPointerDefaultsToReservationTop
  expect "initial rsp override keeps reservation bounds" initialStackPointerOverridePreservesReservation

end Grass.Tests.ISA.X86.SeamNativeReturn

def main : IO Unit := Grass.Tests.ISA.X86.SeamNativeReturn.run
