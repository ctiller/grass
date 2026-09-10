import Grass.Std.Sort.Descriptors

/-! Executable descriptor-sort regressions, not an authored assembly certificate.
Every output below comes from `DescriptorSort.sort?`; expected values only check
that computation. Equal slices deliberately have different source identities.
-/

namespace Grass.Tests.Std.DescriptorSort

open Grass.Std.Logical Grass.Std.Sort

private def source : Vec Byte := Vec.fromList [98, 0, 97, 98, 0]

private def descriptors : Vec Descriptor := Vec.fromList [⟨0, 2⟩, ⟨2, 1⟩, ⟨3, 2⟩]

private def check (name : String) (bytes : Vec Byte) (ranges : Vec Descriptor)
    (expected : Vec DescriptorSort.Occurrence) : IO Unit := do
  unless decide (DescriptorSort.sort? bytes ranges = some expected) do
    throw (IO.userError s!"descriptor-sort regression failed: {name}")

-- These are runtime regression assertions, not proofs of the universal laws.
#eval do
  check "duplicate byte slices" source descriptors
    (Vec.fromList [(1, ⟨2, 1⟩), (0, ⟨0, 2⟩), (2, ⟨3, 2⟩)])
  check "ordinal order differs from offset order" source
    (Vec.fromList [⟨3, 2⟩, ⟨2, 1⟩, ⟨0, 2⟩])
    (Vec.fromList [(1, ⟨2, 1⟩), (0, ⟨3, 2⟩), (2, ⟨0, 2⟩)])
  check "identical empty ranges keep two identities" Vec.empty
    (Vec.fromList [⟨0, 0⟩, ⟨0, 0⟩])
    (Vec.fromList [(0, ⟨0, 0⟩), (1, ⟨0, 0⟩)])
  check "empty input" source Vec.empty Vec.empty
  check "empty range at EOF" source (Vec.fromList [⟨5, 0⟩, ⟨2, 1⟩])
    (Vec.fromList [(0, ⟨5, 0⟩), (1, ⟨2, 1⟩)])
  check "unsigned order, prefix order, CR and non-UTF8 bytes"
    (Vec.fromList [128, 127, 97, 0, 13, 255])
    (Vec.fromList [⟨0, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨4, 2⟩])
    (Vec.fromList [(4, ⟨4, 2⟩), (3, ⟨2, 1⟩), (2, ⟨2, 2⟩),
      (1, ⟨1, 1⟩), (0, ⟨0, 1⟩)])

example : DescriptorSort.sort? source (Vec.fromList [⟨4, 2⟩]) = none := by decide
example : DescriptorSort.sort? source (Vec.fromList [⟨6, 0⟩]) = none := by decide
example : DescriptorSort.sort? source (Vec.fromList [⟨0, 2⟩, ⟨4, 2⟩]) = none := by decide

/-- Representation transport applies universally to the computed output. -/
example (bytes : Vec Byte) (ranges : Vec Descriptor) :
    (DescriptorSort.sort bytes ranges).map (DescriptorSort.decode bytes) =
      ((ranges.mapIdx fun ordinal descriptor => (ordinal, descriptor)).map
        (DescriptorSort.decode bytes)).stableSort
        (fun left right => ByteArray.lexicographicLE left.2 right.2) :=
  DescriptorSort.decode_sort bytes ranges

example {bytes : Vec Byte} {ranges : Vec Descriptor}
    {output : Vec DescriptorSort.Occurrence}
    (checked : DescriptorSort.sort? bytes ranges = some output)
    {occurrence : DescriptorSort.Occurrence} (member : occurrence ∈ output) :
    (occurrence.2.bytes bytes).length = occurrence.2.length :=
  Descriptor.length_bytes_of_valid (DescriptorSort.valid_of_sort?_eq_some checked member)

end Grass.Tests.Std.DescriptorSort
