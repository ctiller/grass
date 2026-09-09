import Grass.Artifact.PE.ImageWriter
import Grass.Artifact.PE.LayoutBinding

/-! Lean-only container-layout fixtures. Payload bytes are opaque and are not
instruction or loader probes. -/

namespace Tests.Artifact.PE.LayoutBinding

open Grass.Artifact.PE Grass.Std.Logical

set_option maxRecDepth 10000

def textName : SectionName :=
  ⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩

def kernel32 : ImportLibrary :=
  { name := Vec.fromList [107, 101, 114, 110, 101, 108, 51, 50, 46, 100, 108, 108]
    symbols := Vec.fromList [{ name := Vec.fromList [69, 120, 105, 116, 80, 114, 111, 99,
      101, 115, 115] }] }

def leftDescription : ExecutableImageDescription :=
  { entryPoint := { sectionIndex := 0, offset := 1 }
    sections := Vec.fromList [
      { name := textName
        contents := Vec.fromList [0x90, 0xc3]
        characteristics := 0x60000020 }]
    imports := Vec.singleton kernel32 }

/-- Same requested shape, with opaque payload bytes changed at a fixed length. -/
def rightDescription : ExecutableImageDescription :=
  { leftDescription with sections := Vec.fromList [
      { name := textName
        contents := Vec.fromList [0xcc, 0xc3]
        characteristics := 0x60000020 }] }

/-- This replacement fails the equal-length premise: the first virtual extent
therefore changes, regardless of any alignment coincidence in later sections. -/
def longerDescription : ExecutableImageDescription :=
  { leftDescription with sections := Vec.fromList [
      { name := textName
        contents := Vec.fromList [0x90, 0xc3, 0x90]
        characteristics := 0x60000020 }] }

def sameLengthObservation : Option (Nat × Nat × Nat × Nat × Bool) := do
  let left ← (prepareImage leftDescription).toOption
  let right ← (prepareImage rightDescription).toOption
  let leftIat ← left.layout.importAddressRva? 0 0
  let rightIat ← right.layout.importAddressRva? 0 0
  some (left.layout.entryPointRva, right.layout.entryPointRva, leftIat, rightIat,
    decide (writeImage left != writeImage right))

def virtualSizeObservation : Option (Nat × Nat) := do
  let left ← (prepareImage leftDescription).toOption
  let longer ← (prepareImage longerDescription).toOption
  let leftSection ← left.layout.placed.get? 0
  let longerSection ← longer.layout.placed.get? 0
  some (leftSection.virtualSpan.size, longerSection.virtualSpan.size)

/-- The two plans retain entry and IAT coordinates while their serialized final
images differ at the replacement payload byte. -/
example : sameLengthObservation = some (0x1001, 0x1001, 0x2028, 0x2028, true) := by
  decide

/-- A changed payload length does not meet the theorem premise and changes its
corresponding placed section virtual extent. -/
example : virtualSizeObservation = some (2, 3) := by
  decide

end Tests.Artifact.PE.LayoutBinding
