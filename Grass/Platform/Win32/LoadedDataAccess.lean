import Grass.Platform.Win32.LoadedAccess

/-!
# Readable spans derived from the checked loaded image

This deterministic selector retains a loaded region containing an entire
numeric read footprint. `DataRoot` is nominally distinct from `CodeRoot`; in
particular, selecting readable data does not classify it as executable or as an
IAT entry. It supplies provenance and placement evidence only. It grants no
access, proves no byte initialized or read, and identifies no API occurrence.
-/

namespace Grass.Platform.Win32.Loader

open Grass.Memory

/-- A readable loaded region contains the complete numeric footprint, and the
footprint's end does not wrap the 64-bit machine address space. -/
def ContainsDataSpan (region : InitializedRegion) (address : MachineAddress)
    (width : Nat) : Prop :=
  region.permission.read = true ∧
    address.toNat + width ≤ 2 ^ 64 ∧
    region.base.toNat ≤ address.toNat ∧
    address.toNat + width ≤ region.base.toNat + region.bytes.length

instance (region : InitializedRegion) (address : MachineAddress) (width : Nat) :
    Decidable (ContainsDataSpan region address width) := by
  unfold ContainsDataSpan
  infer_instance

/-- A selected readable loaded region with membership and whole-span evidence. -/
structure DataRoot {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (address : MachineAddress) (width : Nat) where
  region : InitializedRegion
  member : region ∈ assignedRegions image inputs loaded.patches
  contains : ContainsDataSpan region address width

/-- Deterministically select the first assigned region containing the entire
read footprint. The later CPU access preparation remains responsible for
rechecking the actual record, range, permission, and authority conditions. -/
def LoadedImage.dataRoot? {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (address : MachineAddress) (width : Nat) :
    Option (DataRoot loaded address width) :=
  match found : (assignedRegions image inputs loaded.patches).find?
      (fun region => decide (ContainsDataSpan region address width)) with
  | none => none
  | some region => some
      { region := region
        member := List.mem_of_find?_eq_some found
        contains := by
          have selected := List.find?_some found
          exact of_decide_eq_true selected }

/-- Exact whole-allocation provenance derived from the selected installed record. -/
def DataRoot.provenance {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {address : MachineAddress} {width : Nat}
    (root : DataRoot loaded address width) : Provenance :=
  allocationProvenance root.region.allocId root.region.allocationRecord

/-- The data root names the authoritative allocation record in the actual
loaded initial memory. -/
theorem DataRoot.present {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {address : MachineAddress} {width : Nat}
    (root : DataRoot loaded address width) :
    loaded.initialState.machine.memory.allocations.lookup root.provenance.root =
      some root.region.allocationRecord :=
  (loaded.imagePresent root.region root.member).1

theorem DataRoot.readable {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {address : MachineAddress} {width : Nat}
    (root : DataRoot loaded address width) : root.region.permission.read = true :=
  root.contains.1

theorem DataRoot.span_no_wrap {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {address : MachineAddress} {width : Nat}
    (root : DataRoot loaded address width) : address.toNat + width ≤ 2 ^ 64 :=
  root.contains.2.1

theorem DataRoot.span_contained {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {address : MachineAddress} {width : Nat}
    (root : DataRoot loaded address width) :
    root.region.base.toNat ≤ address.toNat ∧
      address.toNat + width ≤ root.region.base.toNat + root.region.bytes.length :=
  root.contains.2.2

end Grass.Platform.Win32.Loader
