import Grass.Memory.AddressSpace

/-!
# Canonical x86 linear addresses

The currently active paging mode determines whether bit 47 or bit 56 is the
sign bit of a canonical linear address. This leaf records canonicality of
unmasked linear addresses and non-wrapping spans; address translation and fault
classification remain separate.

The 48-bit and 57-bit forms follow Intel's *5-Level Paging and 5-Level EPT*,
<https://cdrdv2-public.intel.com/671442/5-level-paging-white-paper.pdf>.
-/

namespace Grass.ISA.X86

open Grass.Memory

inductive LinearAddressMode where
  | bits48
  | bits57
deriving DecidableEq, Repr

namespace LinearAddressMode

/-- Width of the implemented low portion, including its sign bit. -/
def width : LinearAddressMode → Nat
  | .bits48 => 48
  | .bits57 => 57

end LinearAddressMode

/-- A 64-bit address is the sign extension of the implemented address width. -/
def Canonical (mode : LinearAddressMode) (address : MachineAddress) : Prop :=
  address = BitVec.signExtend 64 (BitVec.setWidth mode.width address)

instance (mode : LinearAddressMode) (address : MachineAddress) :
    Decidable (Canonical mode address) := by
  unfold Canonical
  infer_instance

theorem canonical_iff_signExtend (mode : LinearAddressMode)
    (address : MachineAddress) :
    Canonical mode address ↔
      address = BitVec.signExtend 64 (BitVec.setWidth mode.width address) := by
  rfl

/-- Every byte of the span is canonical, and ordinary natural addition does
not pass the 64-bit address-space limit. -/
def CanonicalSpan (mode : LinearAddressMode) (address : MachineAddress)
    (size : Nat) : Prop :=
  address.toNat + size ≤ 2 ^ 64 ∧
    ∀ offset : Fin size,
      Canonical mode (BitVec.ofNat 64 (address.toNat + offset))

instance (mode : LinearAddressMode) (address : MachineAddress) (size : Nat) :
    Decidable (CanonicalSpan mode address size) := by
  unfold CanonicalSpan
  infer_instance

theorem canonical_of_lt_two_pow_47 (mode : LinearAddressMode)
    {address : MachineAddress} (bound : address.toNat < 2 ^ 47) :
    Canonical mode address := by
  cases mode
  · have msbFalse : (BitVec.setWidth 48 address).msb = false := by
      rw [BitVec.msb_eq_decide]
      simp [BitVec.toNat_setWidth]
      omega
    apply BitVec.eq_of_toNat_eq
    simp [LinearAddressMode.width, BitVec.toNat_signExtend,
      BitVec.toNat_setWidth, msbFalse]
    calc
      address.toNat = address.toNat % 281474976710656 :=
        (Nat.mod_eq_of_lt (by omega)).symm
      _ = (address.toNat % 281474976710656) % 18446744073709551616 :=
        (Nat.mod_eq_of_lt (by
          have := Nat.mod_lt address.toNat (by decide : 0 < 281474976710656)
          omega)).symm
  · have msbFalse : (BitVec.setWidth 57 address).msb = false := by
      rw [BitVec.msb_eq_decide]
      simp [BitVec.toNat_setWidth]
      omega
    apply BitVec.eq_of_toNat_eq
    simp [LinearAddressMode.width, BitVec.toNat_signExtend,
      BitVec.toNat_setWidth, msbFalse]
    calc
      address.toNat = address.toNat % 144115188075855872 :=
        (Nat.mod_eq_of_lt (by omega)).symm
      _ = (address.toNat % 144115188075855872) % 18446744073709551616 :=
        (Nat.mod_eq_of_lt (by
          have := Nat.mod_lt address.toNat (by decide : 0 < 144115188075855872)
          omega)).symm

theorem canonicalSpan_of_end_le_two_pow_47 (mode : LinearAddressMode)
    {address : MachineAddress} {size : Nat}
    (bound : address.toNat + size ≤ 2 ^ 47) :
    CanonicalSpan mode address size := by
  constructor
  · omega
  · intro offset
    apply canonical_of_lt_two_pow_47 mode
    simp only [BitVec.toNat_ofNat]
    have sumLt : address.toNat + offset < 2 ^ 47 := by
      have := offset.isLt
      omega
    rw [Nat.mod_eq_of_lt]
    · exact sumLt
    · omega

theorem canonical48_implies_canonical57 {address : MachineAddress}
    (canonical : Canonical .bits48 address) : Canonical .bits57 address := by
  rw [canonical]
  ext i hi
  by_cases h48 : i < 48
  · have h57 : i < 57 := by omega
    simp [LinearAddressMode.width, BitVec.getElem_signExtend, h48, h57, hi]
  · by_cases h57 : i < 57
    · simp [LinearAddressMode.width, BitVec.getElem_signExtend, h48, h57, hi]
    · simp [LinearAddressMode.width, BitVec.getElem_signExtend,
        BitVec.msb_setWidth, h48, h57]

end Grass.ISA.X86
