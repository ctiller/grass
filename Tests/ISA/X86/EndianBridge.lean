import Grass.ISA.X86.EndianBridge

namespace Grass.Tests.ISA.X86.EndianBridge

open Grass.ISA.X86 Grass.Std.Logical

/- The shared writer cannot silently reverse the four x86 bytes: the bridge
reduces this concrete regression control to x86's canonical `78 56 34 12`. -/
example :
    Grass.Artifact.Binary.writeLittleEndian (count := 4) (0x12345678 : BitVec 32) ≠
      Vec.fromList [0x12, 0x34, 0x56, 0x78] := by
  rw [← le32_writeLittleEndian]
  decide

end Grass.Tests.ISA.X86.EndianBridge
