import Grass.ISA.X86.EndianBridge
import Grass.Artifact.PE.Exceptions
import Grass.ABI.Win64.UnwindBytes

/-! Adapter between the ABI and PE views of one already-resolved
runtime-function record. It reuses both serializers and adds no validity claim. -/
namespace Grass.Assembly.SourceRuntimeFunction

open Grass.ABI.Win64 Grass.Artifact.PE Grass.Std.Logical

/-- The ABI record containing exactly the three checked PE RVA fields. -/
def abiRecord (resolved : ResolvedRuntimeFunction) : RuntimeFunction :=
  { begin_ := BitVec.ofNat 32 resolved.beginRva
    end_ := BitVec.ofNat 32 resolved.endRva
    unwindInfo := BitVec.ofNat 32 resolved.unwindRva }

/-- The existing ABI serializer and PE writer agree byte-for-byte. -/
theorem bytes_exact (resolved : ResolvedRuntimeFunction) :
    Vec.fromList (abiRecord resolved).toBytes = writeRuntimeFunction resolved := by
  change Vec.fromList (Grass.ISA.X86.le32 (BitVec.ofNat 32 resolved.beginRva)) ++
      Vec.fromList (Grass.ISA.X86.le32 (BitVec.ofNat 32 resolved.endRva)) ++
      Vec.fromList (Grass.ISA.X86.le32 (BitVec.ofNat 32 resolved.unwindRva)) = _
  rw [Grass.ISA.X86.le32_writeLittleEndian,
    Grass.ISA.X86.le32_writeLittleEndian, Grass.ISA.X86.le32_writeLittleEndian]
  rfl

/-- Successful extent resolution makes every conversion to the ABI record lossless. -/
theorem fields_lossless {placed : Vec PlacedSection} {binding : RuntimeFunctionBinding}
    {resolved : ResolvedRuntimeFunction}
    (success : resolveRuntimeFunction? placed binding = some resolved) :
    (abiRecord resolved).begin_.toNat = resolved.beginRva ∧
      (abiRecord resolved).end_.toNat = resolved.endRva ∧
      (abiRecord resolved).unwindInfo.toNat = resolved.unwindRva := by
  have bounds := resolveRuntimeFunction?_bounds success
  simp only [abiRecord, BitVec.toNat_ofNat]
  constructor
  · exact Nat.mod_eq_of_lt bounds.1
  constructor
  · exact Nat.mod_eq_of_lt bounds.2.1
  · exact Nat.mod_eq_of_lt bounds.2.2

end Grass.Assembly.SourceRuntimeFunction
