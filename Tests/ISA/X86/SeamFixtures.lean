import Grass.ISA.X86.Target

namespace Grass.Tests.ISA.X86.SeamFixtures

open Grass.ISA.X86
open Grass.ISA.X86.Target
open Grass.Target (StepOutcome)

def codeBase : Nat := 0x100

def region (base size : Nat) (readable writable executable : Bool) : Region :=
  { base := base, size := size, readable := readable, writable := writable,
    executable := executable }

def blankState (instr : Instr) (regs : Gpr → UInt64) (extra : List Region) : State :=
  let code := encode instr
  ({ reg := regs, rip := codeBase, mem := fun _ => none,
     regions := region codeBase code.length true false true :: extra } : State).writeBytes codeBase code

def withBytes (s : State) (writes : List (Nat × List UInt8)) : State :=
  writes.foldl (fun st w => st.writeBytes w.1 w.2) s

def regs (updates : List (Gpr × UInt64)) : Gpr → UInt64 :=
  fun r => (updates.lookup r).getD 0

def internal? : StepOutcome State NativeCall NativeReturn Fault → Option State
  | .internal s => some s
  | _ => none

def isReadFault (address : Nat) : StepOutcome State NativeCall NativeReturn Fault → Bool
  | .fault (.readOutsideImage a) => a == address
  | _ => false

def isWriteFault (address : Nat) : StepOutcome State NativeCall NativeReturn Fault → Bool
  | .fault (.writeOutsideImage a) => a == address
  | _ => false

def expect (name : String) (ok : Bool) : IO Unit :=
  if ok then pure () else throw <| IO.userError s!"seam fixture failed: {name}"

end Grass.Tests.ISA.X86.SeamFixtures
