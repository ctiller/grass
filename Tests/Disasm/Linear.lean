import Grass.Disasm.Linear

namespace Grass.Tests.Disasm
open Grass.Disasm Grass.ISA.X86 Grass.Std.Logical

-- Production PUSH followed by SUB RSP; the suffix is not reinterpreted after refusal.
example : (scan 3 4096 [0x53, 0x48, 0x83, 0xec, 0x20]).consumed =
    [0x53, 0x48, 0x83, 0xec, 0x20] := by decide +kernel

example : (scan 3 4096 [0x53, 0x0f, 0xff, 0x53]).remaining =
    [0x0f, 0xff, 0x53] := by decide +kernel

example : (scan 1 4096 [0x53, 0x53]).stop = some .budget := by decide +kernel

example : (scan 3 4096 [0x48, 0x83]).consumed = [] := by decide +kernel

-- A cursor overflow is a profile refusal, not a wrapped address in the listing.
example : (scan 1 (BitVec.ofNat 64 (2^64-1)) [0x53]).stop =
    some (.decode .fallthroughWrap) := by decide +kernel

example (fuel : Nat) (pc : BitVec 64) (bytes : ByteSeq) :
    (scan fuel pc bytes).consumed ++ (scan fuel pc bytes).remaining = bytes :=
  (scan fuel pc bytes).partition

end Grass.Tests.Disasm
