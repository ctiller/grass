import Grass.Assembly.Store32

/-!
# Store32 local-address recovery

This module exposes the `LocalAddress.Result` used by a successful `Store32`
resolution. It supplies the range and operand equalities needed to reuse the
generic frame-addressing bridge without reconstructing a second address.
-/

namespace Grass.Assembly.Store32

/-- A successful store resolution carries the exact successful local-address
resolution used to construct it. Its input, displacement, operand, and byte range
are the corresponding views of that one address. -/
theorem localAddress_of_resolve? {layout : Grass.ABI.Win64.CallFrameLayout}
    {rspRootOffset : Nat}
    {env : SlotEnv} {input : Input} {resolved : Resolved}
    (success : resolve? layout rspRootOffset env input = some resolved) :
    ∃ address : LocalAddress.Result,
      LocalAddress.resolve? layout rspRootOffset env input.slot 4 = some address ∧
      resolved.input = input ∧
      resolved.displacement = address.displacement ∧
      resolved.operand = address.operand ∧
      resolved.range = address.range := by
  unfold resolve? at success
  split at success <;> try contradiction
  rename_i address addressExact
  split at success <;> try contradiction
  cases success
  obtain ⟨layoutExact, rootExact, _, widthExact, _⟩ :=
    LocalAddress.resolve?_exact addressExact
  refine ⟨address, addressExact, rfl, ?_, ?_, ?_⟩
  · simp [Resolved.displacement, LocalAddress.Result.displacement, layoutExact]
  · simp [Resolved.operand, LocalAddress.Result.operand, Resolved.displacement,
      LocalAddress.Result.displacement, layoutExact]
  · simp [Resolved.range, LocalAddress.Result.range, Resolved.displacement,
      LocalAddress.Result.displacement, layoutExact, rootExact, widthExact]

/-- `signExtend_displacement_of_resolve?` carries the checked local displacement
through the signed immediate interpretation used by the actual x86 operand. -/
theorem signExtend_displacement_of_resolve? {layout : Grass.ABI.Win64.CallFrameLayout}
    {rspRootOffset : Nat} {env : SlotEnv} {input : Input} {resolved : Resolved}
    (success : resolve? layout rspRootOffset env input = some resolved) :
    BitVec.signExtend 64 (BitVec.ofNat 32 resolved.displacement) =
      BitVec.ofNat 64 resolved.displacement := by
  obtain ⟨address, _, _, displacement, _, _⟩ := localAddress_of_resolve? success
  rw [displacement]
  unfold BitVec.signExtend
  rw [address.signed_displacement]
  rfl

end Grass.Assembly.Store32
