import Grass.Platform.Win32.ApiRequest
import Grass.Platform.Win32.WriteFileCallPlan

/-!
# Data retained across a pending Windows call

The actual CallId indexes this data alongside the protocol's request and grant
identities. It contains no CPU, event log, history or target-adequacy witness.
Fixed endpoint transitions must initialize, preserve and consume it using the
actual call and provider receipts. Raw construction alone establishes nothing.
-/

namespace Grass.Platform.Win32

open Grass.ISA.X86 Grass.ABI Grass.Std.Logical

/-- Values of the existing ABI's preserved GPRs, excluding separately tracked
RSP. This does not extend the current ABI table to SIMD or other registers. -/
abbrev NonvolatileSnapshot :=
  { register : Gpr // register ∈ Win64.nonvolatileRegisters ∧ register ≠ .rsp } → BitVec 64

/-- Project only the required preserved GPR values from an actual register file. -/
def captureNonvolatile (gpr : Gpr → BitVec 64) : NonvolatileSnapshot :=
  fun register => gpr register.val

/-- Immutable return coordinates shared by the returning endpoints. The
request, caller/provider identities and loan IDs remain in protocol metadata. -/
structure ReturnFrame where
  entryRsp : BitVec 64
  continuation : BitVec 64
  returnSlot : WriteFile.Argument
  homeSlot : WriteFile.Argument
  saved : NonvolatileSnapshot

/-- Compute the expected post-pop RSP. The endpoint must prove nonwrapping
addition and agreement with the actual pre-CALL RSP before using it. -/
def ReturnFrame.restoredRsp (frame : ReturnFrame) : BitVec 64 :=
  frame.entryRsp + BitVec.ofNat 64 WriteFile.Abi.returnAddressBytes

/-- WriteFile additionally retains its fifth argument and accepted frontier.
Only the frontier changes during provider servicing. -/
structure WriteFileRuntime extends ReturnFrame where
  fifthSlot : WriteFile.Argument
  accepted : Nat

/-- Derive the one fixed ABI extension from the stored coordinates. No second,
independently editable loan plan is stored beside them. -/
def WriteFileRuntime.loanPlan (runtime : WriteFileRuntime) : WriteFile.LoanPlan :=
  ⟨WriteFile.Abi.stackRequests runtime.returnSlot runtime.homeSlot runtime.fifthSlot⟩

/-- Endpoint-specific runtime data; a terminal API has no fabricated return frame. -/
inductive CallRuntime where
  | getStdHandle (frame : ReturnFrame)
  | writeFile (runtime : WriteFileRuntime)
  | exitProcess

/-- The runtime variant agrees with the request retained by the protocol.
Further frame, publication and issuance invariants belong to fixed endpoints. -/
def CallRuntime.MatchesRequest : CallRuntime → ApiRequest → Prop
  | .getStdHandle _, .getStdHandle _ => True
  | .writeFile _, .writeFile _ => True
  | .exitProcess, .exitProcess _ => True
  | _, _ => False

abbrev CallRuntimeTable := FiniteMap Grass.Op.CallProtocol.CallId CallRuntime

end Grass.Platform.Win32
