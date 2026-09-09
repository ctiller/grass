import Grass.Memory.State
import Grass.Memory.SpatialRange

/-!
# Spatial evidence for an independently established write attempt

`PlacedObject` binds the object's declared extent to the actual live allocation
and backing records. `WriteFootprint` describes a nonwrapping machine range; it
does not establish that an instruction attempted or committed a write.

Consumers supply exact instruction/entry evidence, feasible concrete reachability,
and a history-consistent pointer-to-object contract at this same memory state.
`outsideIndex?_sound` then supplies a byte outside that object's machine addresses.
No successful access admission or checker denial is used as a violation witness.
-/

namespace Grass.Memory.SpatialAccess

/-- A live object's own extent, with placement from its resolved allocation. -/
structure PlacedObject (state : MemoryState) (provenance : Provenance) where
  resolved : state.ResolvedAccess provenance provenance.extent
  base : MachineAddress
  placed : resolved.allocation.base = some base
  noWrap : FitsAllocation base resolved.allocation.extent.stop

/-- A candidate write range. Actual attempted-write evidence belongs to the ISA
and concrete execution connection, not this spatial structure. -/
structure WriteFootprint where
  address : MachineAddress
  size : Nat
  noWrap : FitsAllocation address size

/-- The object's numeric range, derived from its checked placement and extent. -/
def PlacedObject.numericExtent {state : MemoryState} {provenance : Provenance}
    (object : PlacedObject state provenance) : ByteRange :=
  provenance.extent.shift object.base.toNat

/-- The candidate's numeric range; `WriteFootprint.noWrap` relates it to addresses. -/
def WriteFootprint.numericRange (write : WriteFootprint) : ByteRange :=
  ⟨write.address.toNat, write.size⟩

/-- `PlacedObject.address_covered` connects each legal object offset to placement. -/
theorem PlacedObject.address_covered {state : MemoryState} {provenance : Provenance}
    (object : PlacedObject state provenance) {offset : Nat}
    (covered : provenance.extent.Covers offset) :
    object.numericExtent.Covers (addressOf object.base offset).toNat := by
  have within := object.resolved.coordinates.withinView
  have bounded : offset < object.resolved.allocation.extent.stop := by
    unfold ByteRange.Contains at within
    unfold ByteRange.Covers at covered
    omega
  rw [toNat_addressOf object.noWrap bounded]
  change object.base.toNat + provenance.extent.start ≤ object.base.toNat + offset ∧
    object.base.toNat + offset < object.base.toNat + provenance.extent.start + provenance.extent.size
  unfold ByteRange.Covers ByteRange.stop at covered
  omega

/-- Candidate byte index computed by the pure range checker. Its spatial meaning
is established by `outsideIndex?_sound`, not by an audit-denial classification. -/
def outsideIndex? {state : MemoryState} {provenance : Provenance}
    (object : PlacedObject state provenance) (write : WriteFootprint) : Option Nat :=
  ByteRange.firstOutsideIndex? object.numericExtent write.numericRange

/-- A byte of the supplied footprint differs from every legal object address.
`outsideIndex?_sound` constructs this evidence from a successful index check. -/
structure OutsideByte {state : MemoryState} {provenance : Provenance}
    (object : PlacedObject state provenance) (write : WriteFootprint) (index : Nat) : Prop where
  touched : index < write.size
  outside : ∀ offset, provenance.extent.Covers offset →
    addressOf write.address index ≠ addressOf object.base offset

/-- `outsideIndex?_sound` exposes an actual addressed byte outside the supplied
object. Establishing that a concrete instruction attempts this footprint remains
the consumer's separate, reached-state-indexed obligation. -/
theorem outsideIndex?_sound {state : MemoryState} {provenance : Provenance}
    (object : PlacedObject state provenance) (write : WriteFootprint) {index : Nat}
    (checked : outsideIndex? object write = some index) :
    OutsideByte object write index := by
  obtain ⟨touched, outside⟩ := ByteRange.firstOutsideIndex?_some_sound checked
  change index < write.size at touched
  refine ⟨touched, ?_⟩
  intro offset covered equalAddress
  have legal := object.address_covered covered
  rw [← equalAddress, toNat_addressOf write.noWrap touched] at legal
  exact outside legal

/-- Numeric coverage of each addressed byte; `outsideIndex?_eq_none_iff` makes
this the precise safe result of the spatial checker, including empty footprints. -/
def WithinObject {state : MemoryState} {provenance : Provenance}
    (object : PlacedObject state provenance) (write : WriteFootprint) : Prop :=
  ∀ index, index < write.size →
    object.numericExtent.Covers (addressOf write.address index).toNat

/-- `outsideIndex?_eq_none_iff` characterizes spatial coverage only, not authority,
initialization, attempted execution, or successful write completion. -/
theorem outsideIndex?_eq_none_iff {state : MemoryState} {provenance : Provenance}
    (object : PlacedObject state provenance) (write : WriteFootprint) :
    outsideIndex? object write = none ↔ WithinObject object write := by
  rw [outsideIndex?, ByteRange.firstOutsideIndex?_eq_none_iff]
  constructor
  · intro covered index touched
    rw [toNat_addressOf write.noWrap touched]
    exact covered index touched
  · intro covered index touched
    have atIndex := covered index touched
    rw [toNat_addressOf write.noWrap touched] at atIndex
    exact atIndex

/-- `WithinObject.address_witness` recovers an object-local offset for each covered
address, using the already checked placement rather than inventing provenance. -/
theorem WithinObject.address_witness {state : MemoryState} {provenance : Provenance}
    {object : PlacedObject state provenance} {write : WriteFootprint}
    (within : WithinObject object write) {index : Nat} (touched : index < write.size) :
    ∃ offset, provenance.extent.Covers offset ∧
      addressOf object.base offset = addressOf write.address index := by
  have covered := within index touched
  rw [toNat_addressOf write.noWrap touched] at covered
  change object.base.toNat + provenance.extent.start ≤ write.address.toNat + index ∧
    write.address.toNat + index < object.base.toNat + provenance.extent.start + provenance.extent.size at covered
  let offset := write.address.toNat + index - object.base.toNat
  have localCovered : provenance.extent.Covers offset := by
    unfold ByteRange.Covers ByteRange.stop offset
    omega
  refine ⟨offset, localCovered, ?_⟩
  have root := object.resolved.coordinates.withinView
  have bounded : offset < object.resolved.allocation.extent.stop := by
    unfold ByteRange.Contains at root
    unfold ByteRange.Covers at localCovered
    omega
  apply BitVec.eq_of_toNat_eq
  rw [toNat_addressOf object.noWrap bounded, toNat_addressOf write.noWrap touched]
  unfold offset
  omega

/-- `OutsideByte.not_within` refutes the exact spatial coverage property checked
by `outsideIndex?_eq_none_iff`; it does not refute unrelated safety properties. -/
theorem OutsideByte.not_within {state : MemoryState} {provenance : Provenance}
    {object : PlacedObject state provenance} {write : WriteFootprint} {index : Nat}
    (witness : OutsideByte object write index) : ¬ WithinObject object write := by
  intro within
  obtain ⟨offset, covered, equalAddress⟩ := within.address_witness witness.touched
  exact witness.outside offset covered equalAddress.symm

end Grass.Memory.SpatialAccess
