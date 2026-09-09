import Grass.ISA.X86.LinearAddress

namespace Grass.Tests.ISA.X86.LinearAddress

open Grass.Memory Grass.ISA.X86

example : Canonical .bits48 (BitVec.ofNat 64 0x7fff_ffff_ffff) := by decide
example : Canonical .bits57 (BitVec.ofNat 64 0x7fff_ffff_ffff) := by decide
example : ¬ Canonical .bits48 (BitVec.ofNat 64 0x0000_8000_0000_0000) := by decide
example : Canonical .bits48 (BitVec.ofNat 64 0xffff_8000_0000_0000) := by decide

example : CanonicalSpan .bits48 (BitVec.ofNat 64 0x1000) 16 := by decide
example : ¬ CanonicalSpan .bits48 (BitVec.ofNat 64 0xffff_ffff_ffff_fff8) 16 := by
  decide

example {address : MachineAddress} (bound : address.toNat < 2 ^ 47) :
    Canonical .bits48 address ∧ Canonical .bits57 address :=
  ⟨canonical_of_lt_two_pow_47 .bits48 bound,
    canonical_of_lt_two_pow_47 .bits57 bound⟩

example {address : MachineAddress} (canonical : Canonical .bits48 address) :
    Canonical .bits57 address := canonical48_implies_canonical57 canonical

end Grass.Tests.ISA.X86.LinearAddress
