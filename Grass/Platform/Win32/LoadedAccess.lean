import Grass.Platform.Win32.LoaderEntry

/-!
# Access roots derived from the checked loader state

Code selection is a deterministic search of the actual assigned image regions.
Stack provenance comes from the existing allocation checked by initialization.
These roots identify storage; they do not establish instruction fetch, frame
authority, Windows page coverage, or architectural fault completeness.
-/

namespace Grass.Platform.Win32.Loader

open Grass.Core Grass.Memory Grass.ISA.X86

/-- Whole-allocation provenance computed from an authoritative allocation record. -/
def allocationProvenance (id : AllocId) (record : AllocationRecord) : Provenance :=
  { space := record.space, root := id, epoch := record.epoch, source := record.source
    rootExtent := record.extent, path := [] }

/-- The logical executable region contains the instruction's first byte. The
complete fetched encoding still has to pass the CPU access checks. -/
def ContainsCodeAddress (region : InitializedRegion) (address : MachineAddress) : Prop :=
  region.permission.execute = true ∧ region.base.toNat ≤ address.toNat ∧
    address.toNat < region.base.toNat + region.bytes.length

instance (region : InitializedRegion) (address : MachineAddress) :
    Decidable (ContainsCodeAddress region address) := by
  unfold ContainsCodeAddress
  infer_instance

/-- A selected loaded region, retaining membership and address evidence. -/
structure CodeRoot {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (address : MachineAddress) where
  region : InitializedRegion
  member : region ∈ assignedRegions image inputs loaded.patches
  contains : ContainsCodeAddress region address

/-- Compute the code root without accepting caller-supplied provenance. -/
def LoadedImage.codeRoot? {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) (address : MachineAddress) :
    Option (CodeRoot loaded address) :=
  match found : (assignedRegions image inputs loaded.patches).find?
      (fun region => decide (ContainsCodeAddress region address)) with
  | none => none
  | some region => some
      { region := region
        member := List.mem_of_find?_eq_some found
        contains := by
          have selected := List.find?_some found
          exact of_decide_eq_true selected }

/-- Exact code provenance from the selected installed record. -/
def CodeRoot.provenance {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {address : MachineAddress}
    (root : CodeRoot loaded address) : Provenance :=
  allocationProvenance root.region.allocId root.region.allocationRecord

/-- The code root names the authoritative record in the canonical initial state. -/
theorem CodeRoot.present {image : ImageInput} {inputs : EntryInputs}
    {loaded : LoadedImage image inputs} {address : MachineAddress}
    (root : CodeRoot loaded address) :
    loaded.initialState.machine.memory.allocations.lookup root.provenance.root =
      some root.region.allocationRecord :=
  (loaded.imagePresent root.region root.member).1

/-- Stack records are recovered from the actual initialized allocation table. -/
def LoadedImage.stackProvenance? {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) : Option Provenance :=
  (loaded.memory.allocations.lookup inputs.stack.allocation).map
    (allocationProvenance inputs.stack.allocation)

/-- `stackProvenance_present` derives projection presence from checked
initialization, retaining the actual stack allocation's epoch, source and extent. -/
theorem LoadedImage.stackProvenance_present {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    ∃ record, loaded.memory.allocations.lookup inputs.stack.allocation = some record ∧
      loaded.stackProvenance? = some (allocationProvenance inputs.stack.allocation record) ∧
      record.live = true ∧ record.space = .cpuVirtual ∧ record.source = .stack ∧
      inputs.thread ∈ record.owners ∧ record.permission = .readWrite := by
  obtain ⟨record, present, valid⟩ := loaded.stack
  change loaded.memory.allocations.lookup inputs.stack.allocation = some record at present
  exact ⟨record, present, by simp [stackProvenance?, present],
    valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1, valid.2.2.2.2.1⟩

/-- The CPU caller is the registered thread checked by the loader. -/
theorem LoadedImage.thread_present {image : ImageInput} {inputs : EntryInputs}
    (loaded : LoadedImage image inputs) :
    loaded.initialState.machine.contexts.lookup inputs.thread = some .thread :=
  loaded.environment.1

end Grass.Platform.Win32.Loader
