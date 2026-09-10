import Grass.ISA.Wasm.LocalStep

namespace Grass.Tests.ISA.Wasm
open Grass.ISA.Wasm

/-- Validation fixture only: emitted by the same producer used by Artifact. -/
def source : Module :=
  { imports := [⟨"env", "observe", ⟨[.i32, .i32], [.i32]⟩⟩]
    functions := [⟨⟨[], [.i32]⟩, [],
      [.i32Const 7, .i32Const 3, .i32Sub, .i32Const 5, .call 0]⟩]
    exports := [⟨"run", 1⟩] }

def artifact : Artifact := (Artifact.emit source).get (by decide)

def store : Store :=
  { modules := [⟨artifact, [⟨0⟩, ⟨1⟩]⟩]
    functions := [.host ⟨[.i32, .i32], [.i32]⟩ ⟨19⟩, .defined ⟨0⟩ 0] }

def before : State := ⟨⟨1⟩, 4, [], [.i32 5, .i32 4]⟩

/-- Independent source-site-to-outcome check, not a direct call to localStep. -/
example : (match LocalRun.check store ⟨⟨1⟩, 2, [], [.i32 3, .i32 7]⟩ with
    | .ok run => run.site.instruction == .i32Sub &&
        run.outcome == .next ⟨⟨1⟩, 3, [], [.i32 4]⟩
    | .error _ => false) = true := by decide

example : (match HostInvocation.check store before with
    | .ok call => call.arguments == [.i32 4, .i32 5] &&
        call.hostId == ⟨19⟩ && call.continuation.pc == 5 && call.continuation.stack == []
    | .error _ => false) = true := by decide

example : (match HostInvocation.check store { before with pc := 3 } with
    | .error .notCall => true | _ => false) = true := by decide

example : (match HostInvocation.check store { before with stack := [.i32 5] } with
    | .error .missingArguments => true | _ => false) = true := by decide

example : (match HostInvocation.check store { before with stack := [.i64 5, .i32 4] } with
    | .error .argumentTypesMismatch => true | _ => false) = true := by decide

example : (match HostInvocation.check
    { store with functions := [.host ⟨[.i64], []⟩ ⟨19⟩, .defined ⟨0⟩ 0] } before with
    | .error .signatureMismatch => true | _ => false) = true := by decide

example : (match HostInvocation.check
    { store with modules := [⟨artifact, [⟨0⟩, ⟨0⟩]⟩] } before with
    | .error .callerBindingMismatch => true | _ => false) = true := by decide

/-- Identical local function indices in two module instances resolve differently. -/
def twoModules : Store :=
  { modules := [⟨artifact, [⟨0⟩, ⟨1⟩]⟩, ⟨artifact, [⟨2⟩, ⟨3⟩]⟩]
    functions := [.host ⟨[.i32, .i32], [.i32]⟩ ⟨19⟩, .defined ⟨0⟩ 0,
      .host ⟨[.i32, .i32], [.i32]⟩ ⟨23⟩, .defined ⟨1⟩ 0] }

example : (match HostInvocation.check twoModules { before with function := ⟨3⟩ } with
    | .ok call => call.hostId == ⟨23⟩ && call.site.moduleAddr == ⟨1⟩
    | _ => false) = true := by decide

example : (Artifact.check source (artifact.bytes ++ [0])).isSome = false := by decide

example : localStep .i32Sub ⟨⟨0⟩, 0, [], [.i32 3, .i32 7]⟩ =
    .ok (.next ⟨⟨0⟩, 1, [], [.i32 4]⟩) := by rfl

example : localStep .i32Add ⟨⟨0⟩, 0, [], [.i32 1, .i32 0xffffffff]⟩ =
    .ok (.next ⟨⟨0⟩, 1, [], [.i32 0]⟩) := by rfl

example : Binary.instruction (.i32Const 0xffffffff) = some [0x41, 0x7f] := by decide
example : Binary.instruction (.i32Const 64) = some [0x41, 0xc0, 0x00] := by decide
example : Binary.u32 (2 ^ 32) = none := by decide

end Grass.Tests.ISA.Wasm
