import Grass.Memory.State
import Grass.Target.Raw

/-!
# The machine-memory seam

`docs/MEMORY_MODEL.md` describes one memory model; every byte-addressed ISA
record built so far carries a *second* one — a flat `Nat → Option UInt8` plus a
permission list — and the two never meet. This module is the interface that lets
them: the byte-addressed operations an ISA `step` needs, the laws an ISA proof
relies on, and two instances of both.

## What is here

- `LoadPlan`: what a loader installs before the first instruction — placed
  sections, a stack, staged bytes, and the MMIO windows an access must be routed
  to instead of touched.
- `MachineMemory`: the operation record. It is a structure and not a class
  because an ISA `State` wants to *contain* a memory, not to be resolved for
  one, and because the two instances below differ in their carrier type; an ISA
  parameterised by `mm : MachineMemory` with a field `mem : mm.Mem` switches
  memory models by changing one term.
- `MachineMemory.Laws`: the eight facts an ISA step proof uses. Read after
  write, framing, commutation of disjoint writes, stability of permissions under
  writes, and the two directions of the permission gate (a denied access is
  `none`, a permitted one is not).
- `Flat`: what the ISA records have today, with every law proved.
- `Mapped`: the same interface backed by `Grass.Memory.MemoryState`, so a load
  resolves provenance, checks the allocation's rights and liveness, and reads
  the allocation's own backing; a store commits through `writeResolved`. Its
  laws are proved one by one below rather than bundled, and the module comment
  on `Mapped` states exactly which are open.

Nothing here names a program, a spike, a platform, or a service domain. It names
`Grass.Target.Section` because that is the vocabulary of a placed image, and
`Grass/Target/Raw.lean` imports nothing.
-/

namespace Grass.Memory

open Grass.Std.Logical

/-! ## Address ranges -/

/-- Two byte ranges given as base and length do not overlap. The frame and
commutation laws below are stated over this rather than over `ByteRange` because
the seam's addresses are machine addresses, not allocation-local offsets. -/
def AddressRangesDisjoint (baseA sizeA baseB sizeB : Nat) : Prop :=
  baseA + sizeA ≤ baseB ∨ baseB + sizeB ≤ baseA

instance (baseA sizeA baseB sizeB : Nat) :
    Decidable (AddressRangesDisjoint baseA sizeA baseB sizeB) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-! ## Device windows and the load plan -/

/-- A memory-mapped device window: an address range whose accesses are the
platform's business, not the memory's. An ISA routes a load or store inside one
to the platform as a native call instead of reading or writing bytes. -/
structure DeviceWindow where
  /-- The lowest address the window occupies. -/
  base : Nat
  /-- The window's size in bytes. -/
  size : Nat
deriving Repr, DecidableEq, Inhabited

/-- Whether an address falls inside the window. -/
def DeviceWindow.covers (window : DeviceWindow) (address : Nat) : Bool :=
  decide (window.base ≤ address ∧ address < window.base + window.size)

/-- Whether an address falls inside a placed section. The Bool spelling, rather
than `Grass.Target.Section.Contains`, is what the region search and the byte
lookup share, so that "the section a loaded byte came from" and "the region that
permits reading it" cannot disagree by construction. -/
def sectionCovers (sec : Grass.Target.Section) (address : Nat) : Bool :=
  decide (sec.virtualAddress ≤ address ∧ address < sec.virtualAddress + sec.bytes.length)

/-- Everything a loader installs before the first instruction runs: the placed
sections of an assembled image, the stack the platform reserved, whatever bytes
the platform staged (an argument block, an auxiliary vector), and the device
windows. This is the ISA-independent half of `Grass.Target.ISA.initial`. -/
structure LoadPlan where
  /-- The image's placed sections, in load order. -/
  sections : List Grass.Target.Section
  /-- The lowest address of the stack region. -/
  stackBase : Nat
  /-- The stack region's size in bytes. -/
  stackSize : Nat
  /-- Bytes the platform placed outside the image, as `(address, bytes)`. -/
  staged : List (Nat × List UInt8)
  /-- Memory-mapped device windows. -/
  devices : List DeviceWindow

namespace LoadPlan

/-- Whether an address lies in the stack region. -/
def stackCovers (plan : LoadPlan) (address : Nat) : Bool :=
  decide (plan.stackBase ≤ address ∧ address < plan.stackBase + plan.stackSize)

/-- The section covering an address, if any. Overlapping sections are a
well-formedness failure an artifact writer refuses
(`Grass.Target.Sectioned.Disjoint`); this picks the first, exactly as the region
search below does. -/
def sectionAt? (plan : LoadPlan) (address : Nat) : Option Grass.Target.Section :=
  plan.sections.find? fun sec => sectionCovers sec address

/-- The image byte at an address, if a section supplies one. -/
def sectionByte? (plan : LoadPlan) (address : Nat) : Option UInt8 :=
  (plan.sectionAt? address).bind fun sec => sec.bytes[address - sec.virtualAddress]?

/-- The staged byte at an address, if the platform placed one. -/
def stagedByte? (plan : LoadPlan) (address : Nat) : Option UInt8 :=
  plan.staged.findSome? fun region =>
    if region.1 ≤ address ∧ address < region.1 + region.2.length then
      region.2[address - region.1]?
    else Option.none

/-- The byte the plan installs at an address: an image byte, else a staged byte,
else zero. Addresses outside every region are still answered, because it is the
region map and never the byte function that decides whether an access is
permitted. -/
def byteAt (plan : LoadPlan) (address : Nat) : UInt8 :=
  match plan.sectionByte? address with
  | some byte => byte
  | Option.none => (plan.stagedByte? address).getD 0

end LoadPlan

/-! ## The seam -/

/--
The byte-addressed memory operations one ISA step needs.

Every field is an operation over an abstract carrier `Mem`. An ISA `State` holds
a `Mem` and asks these questions; it never learns whether the answers came from
a flat array or from a provenance-checked allocation table.
-/
structure MachineMemory where
  /-- The memory representation. -/
  Mem : Type
  /-- Whether an address may be read. -/
  readableAt : Mem → Nat → Bool
  /-- Whether an address may be written. -/
  writableAt : Mem → Nat → Bool
  /-- Whether an address may be fetched from and executed. -/
  executableAt : Mem → Nat → Bool
  /-- Whether an address lies in a device window, so that the access belongs to
  the platform rather than to memory. -/
  deviceAt : Mem → Nat → Bool
  /-- `count` bytes from `address` in ascending address order, or `none` if any
  of them is unmapped or unreadable. -/
  readBytes : Mem → Nat → Nat → Option (List UInt8)
  /-- Write bytes in ascending address order, or `none` if any target address is
  unmapped or unwritable. -/
  writeBytes : Mem → Nat → List UInt8 → Option Mem
  /-- Install an image, a stack, staged bytes, and device windows. -/
  load : LoadPlan → Mem

namespace MachineMemory

variable (mm : MachineMemory)

/-- Every byte of `[address, address + count)` may be read. -/
def readableRange (m : mm.Mem) (address count : Nat) : Bool :=
  (List.range count).all fun offset => mm.readableAt m (address + offset)

/-- Every byte of `[address, address + count)` may be written. -/
def writableRange (m : mm.Mem) (address count : Nat) : Bool :=
  (List.range count).all fun offset => mm.writableAt m (address + offset)

/-- Every byte of `[address, address + count)` may be executed. -/
def executableRange (m : mm.Mem) (address count : Nat) : Bool :=
  (List.range count).all fun offset => mm.executableAt m (address + offset)

/-- Fetch a fixed-width instruction: `count` bytes that are executable as well as
readable. This is the AArch64 and Wasm shape, where an instruction's width is
known before it is read. -/
def fetch (m : mm.Mem) (address count : Nat) : Option (List UInt8) :=
  if mm.executableRange m address count then mm.readBytes m address count else Option.none

/-- Fetch a variable-width instruction: as many consecutive executable, readable
bytes as are available, up to `bound`. This is the x86 shape, where the width is
a result of decoding; stopping short rather than failing lets a short
instruction at the end of a section still decode. -/
def fetchWindow (m : mm.Mem) : Nat → Nat → List UInt8
  | _, 0 => []
  | address, bound + 1 =>
      if mm.executableAt m address then
        match mm.readBytes m address 1 with
        | some [byte] => byte :: fetchWindow m (address + 1) bound
        | _ => []
      else []

/--
The laws an ISA step proof relies on.

Two of them are there to stop the interface from being satisfied vacuously.
`readBytes_isSome` and `writeBytes_isSome` are the positive directions of the
permission gate: without them a memory that refuses everything satisfies every
other law here, and an adequacy proof over it would be about a machine that
cannot run.
-/
structure Laws (mm : MachineMemory) : Prop where
  /-- A successful read returns exactly the bytes it was asked for. -/
  readBytes_length : ∀ (m : mm.Mem) (address count : Nat) (bytes : List UInt8),
    mm.readBytes m address count = some bytes → bytes.length = count
  /-- An unreadable byte anywhere in the range makes the whole read `none`.
  There is no truncated read and no wraparound. -/
  readBytes_eq_none : ∀ (m : mm.Mem) (address count offset : Nat), offset < count →
    mm.readableAt m (address + offset) = false → mm.readBytes m address count = Option.none
  /-- A wholly readable range does read. -/
  readBytes_isSome : ∀ (m : mm.Mem) (address count : Nat),
    mm.readableRange m address count = true → (mm.readBytes m address count).isSome = true
  /-- An unwritable byte anywhere in the range makes the whole write `none`. -/
  writeBytes_eq_none : ∀ (m : mm.Mem) (address offset : Nat) (bytes : List UInt8),
    offset < bytes.length → mm.writableAt m (address + offset) = false →
    mm.writeBytes m address bytes = Option.none
  /-- A wholly writable range does write. -/
  writeBytes_isSome : ∀ (m : mm.Mem) (address : Nat) (bytes : List UInt8),
    mm.writableRange m address bytes.length = true →
    (mm.writeBytes m address bytes).isSome = true
  /-- Permissions are stable under writes: storing bytes never grants or revokes
  read permission anywhere. -/
  readableAt_writeBytes : ∀ (m next : mm.Mem) (address query : Nat) (bytes : List UInt8),
    mm.writeBytes m address bytes = some next →
    mm.readableAt next query = mm.readableAt m query
  /-- Permissions are stable under writes, for write permission. -/
  writableAt_writeBytes : ∀ (m next : mm.Mem) (address query : Nat) (bytes : List UInt8),
    mm.writeBytes m address bytes = some next →
    mm.writableAt next query = mm.writableAt m query
  /-- Permissions are stable under writes, for execute permission. A store never
  makes data executable. -/
  executableAt_writeBytes : ∀ (m next : mm.Mem) (address query : Nat) (bytes : List UInt8),
    mm.writeBytes m address bytes = some next →
    mm.executableAt next query = mm.executableAt m query
  /-- A store never creates or destroys a device window. -/
  deviceAt_writeBytes : ∀ (m next : mm.Mem) (address query : Nat) (bytes : List UInt8),
    mm.writeBytes m address bytes = some next →
    mm.deviceAt next query = mm.deviceAt m query
  /-- Read after write. -/
  readBytes_writeBytes_self : ∀ (m next : mm.Mem) (address : Nat) (bytes : List UInt8),
    mm.writeBytes m address bytes = some next →
    mm.readableRange m address bytes.length = true →
    mm.readBytes next address bytes.length = some bytes
  /-- A write is invisible to a disjoint read. -/
  readBytes_writeBytes_of_disjoint : ∀ (m next : mm.Mem) (address : Nat) (bytes : List UInt8)
      (query count : Nat),
    mm.writeBytes m address bytes = some next →
    AddressRangesDisjoint address bytes.length query count →
    mm.readBytes next query count = mm.readBytes m query count
  /-- Disjoint writes commute, failure included: if one order refuses, so does
  the other. -/
  writeBytes_comm : ∀ (m : mm.Mem) (baseA : Nat) (bytesA : List UInt8) (baseB : Nat)
      (bytesB : List UInt8),
    AddressRangesDisjoint baseA bytesA.length baseB bytesB.length →
    ((mm.writeBytes m baseA bytesA).bind fun next => mm.writeBytes next baseB bytesB) =
      ((mm.writeBytes m baseB bytesB).bind fun next => mm.writeBytes next baseA bytesA)
  /-- An address outside every section and outside the stack is not readable
  after a load. This is what makes an out-of-image access a fault. -/
  readableAt_load_of_unmapped : ∀ (plan : LoadPlan) (address : Nat),
    plan.sectionAt? address = Option.none → plan.stackCovers address = false →
    mm.readableAt (mm.load plan) address = false
  /-- A loaded section's permission bits are the ones the section declared,
  verbatim; the loader does not reinterpret least privilege. -/
  readableAt_load_of_section : ∀ (plan : LoadPlan) (address : Nat)
      (sec : Grass.Target.Section),
    plan.sectionAt? address = some sec →
    mm.readableAt (mm.load plan) address = sec.readable
  /-- A loaded section's execute bit likewise, which is what makes the entry
  address fetchable and a data section not. -/
  executableAt_load_of_section : ∀ (plan : LoadPlan) (address : Nat)
      (sec : Grass.Target.Section),
    plan.sectionAt? address = some sec →
    mm.executableAt (mm.load plan) address = sec.executable
  /-- What a read of a freshly loaded image returns is what the plan installed.
  Without this the loader could install anything. -/
  readBytes_load : ∀ (plan : LoadPlan) (address count : Nat) (bytes : List UInt8),
    mm.readBytes (mm.load plan) address count = some bytes →
    bytes = (List.range count).map fun offset => plan.byteAt (address + offset)
  /-- The device windows after a load are the plan's device windows. -/
  deviceAt_load : ∀ (plan : LoadPlan) (address : Nat),
    mm.deviceAt (mm.load plan) address =
      plan.devices.any fun window => window.covers address

end MachineMemory

/-! ## Range helpers

Both instances gate on `List.all` over `List.range`, so both need these. -/

theorem all_range_eq_false {count offset : Nat} {p : Nat → Bool} (hlt : offset < count)
    (hp : p offset = false) : (List.range count).all p = false := by
  cases hall : (List.range count).all p with
  | false => rfl
  | true =>
      rw [List.all_eq_true] at hall
      have := hall offset (List.mem_range.mpr hlt)
      rw [hp] at this
      exact Bool.noConfusion this

theorem all_range_eq_true {count : Nat} {p : Nat → Bool}
    (h : ∀ offset, offset < count → p offset = true) : (List.range count).all p = true := by
  rw [List.all_eq_true]
  intro x hx
  exact h x (List.mem_range.mp hx)

theorem of_all_range {count offset : Nat} {p : Nat → Bool}
    (hall : (List.range count).all p = true) (hlt : offset < count) : p offset = true := by
  rw [List.all_eq_true] at hall
  exact hall offset (List.mem_range.mpr hlt)

/-! ## The flat instance

What the three ISA records carry today, with the one representational change
their own docstrings ask for: bytes are total (`Nat → UInt8`) and the region map
is the sole authority on access. AArch64's `initial` already gives every mapped
byte a value and x86's docstring already says `step` must never consult `mem`
outside a region, so "mapped but valueless" was an unreachable state that only
made every law need a side condition. -/

/-- A mapped region of the address space: a contiguous range and what may be
done with it. -/
structure Region where
  /-- The lowest address the region occupies. -/
  base : Nat
  /-- The region's size in bytes. -/
  size : Nat
  /-- Whether loaded code may read it. -/
  readable : Bool
  /-- Whether loaded code may write it. -/
  writable : Bool
  /-- Whether loaded code may fetch and execute from it. -/
  executable : Bool
deriving Repr, DecidableEq, Inhabited

/-- Whether an address lies inside the region. -/
def Region.covers (region : Region) (address : Nat) : Bool :=
  decide (region.base ≤ address ∧ address < region.base + region.size)

/-- Flat byte-addressed memory with a region map. -/
structure Flat where
  /-- The byte at every address. Access is decided by `regions`, never here. -/
  bytes : Nat → UInt8
  /-- The mapped regions, searched in order. -/
  regions : List Region
  /-- The device windows. -/
  devices : List DeviceWindow

namespace Flat

/-- The region containing an address, if any. -/
def regionAt (flat : Flat) (address : Nat) : Option Region :=
  flat.regions.find? fun region => region.covers address

/-- Whether an address may be read. -/
def readableAt (flat : Flat) (address : Nat) : Bool :=
  (flat.regionAt address).elim false Region.readable

/-- Whether an address may be written. -/
def writableAt (flat : Flat) (address : Nat) : Bool :=
  (flat.regionAt address).elim false Region.writable

/-- Whether an address may be executed. -/
def executableAt (flat : Flat) (address : Nat) : Bool :=
  (flat.regionAt address).elim false Region.executable

/-- Whether an address lies in a device window. -/
def deviceAt (flat : Flat) (address : Nat) : Bool :=
  flat.devices.any fun window => window.covers address

/-- Every byte of a range may be read. -/
def readableRange (flat : Flat) (address count : Nat) : Bool :=
  (List.range count).all fun offset => flat.readableAt (address + offset)

/-- Every byte of a range may be written. -/
def writableRange (flat : Flat) (address count : Nat) : Bool :=
  (List.range count).all fun offset => flat.writableAt (address + offset)

/-- Overlay `bytes` at `address` onto a byte function. -/
def writeAt (base : Nat → UInt8) (address : Nat) (bytes : List UInt8) : Nat → UInt8 :=
  fun query =>
    if h : address ≤ query ∧ query < address + bytes.length then
      bytes[query - address]'(by omega)
    else base query

/-- Read a range, or refuse it. -/
def readBytes (flat : Flat) (address count : Nat) : Option (List UInt8) :=
  if flat.readableRange address count then
    some ((List.range count).map fun offset => flat.bytes (address + offset))
  else Option.none

/-- Write a range, or refuse it. -/
def writeBytes (flat : Flat) (address : Nat) (bytes : List UInt8) : Option Flat :=
  if flat.writableRange address bytes.length then
    some { flat with bytes := writeAt flat.bytes address bytes }
  else Option.none

/-- The region a placed section becomes: its own address, size, and permission
bits, unreinterpreted. -/
def sectionRegion (sec : Grass.Target.Section) : Region :=
  { base := sec.virtualAddress, size := sec.bytes.length, readable := sec.readable,
    writable := sec.writable, executable := sec.executable }

/-- The region the stack becomes: readable, writable, and never executable. -/
def stackRegion (plan : LoadPlan) : Region :=
  { base := plan.stackBase, size := plan.stackSize, readable := true, writable := true,
    executable := false }

/-- Install a plan. -/
def load (plan : LoadPlan) : Flat :=
  { bytes := plan.byteAt
    regions := plan.sections.map sectionRegion ++ [stackRegion plan]
    devices := plan.devices }

/-! ### Laws -/

@[simp] theorem readableRange_setBytes (flat : Flat) (f : Nat → UInt8) (address count : Nat) :
    ({ flat with bytes := f } : Flat).readableRange address count =
      flat.readableRange address count := rfl

@[simp] theorem writableRange_setBytes (flat : Flat) (f : Nat → UInt8) (address count : Nat) :
    ({ flat with bytes := f } : Flat).writableRange address count =
      flat.writableRange address count := rfl

/-- What a successful write produced: the region and device maps are untouched
and the bytes are the overlay. -/
theorem writeBytes_eq_some {flat next : Flat} {address : Nat} {bytes : List UInt8}
    (h : flat.writeBytes address bytes = some next) :
    next.regions = flat.regions ∧ next.devices = flat.devices ∧
      next.bytes = writeAt flat.bytes address bytes := by
  unfold writeBytes at h
  split at h
  · injection h with h
    subst h
    exact ⟨rfl, rfl, rfl⟩
  · simp at h

theorem writableRange_of_writeBytes {flat next : Flat} {address : Nat} {bytes : List UInt8}
    (h : flat.writeBytes address bytes = some next) :
    flat.writableRange address bytes.length = true := by
  unfold writeBytes at h
  split at h
  · assumption
  · simp at h

theorem regionAt_congr {flat next : Flat} (h : next.regions = flat.regions) (address : Nat) :
    next.regionAt address = flat.regionAt address := by
  unfold regionAt
  rw [h]

theorem readBytes_length {flat : Flat} {address count : Nat} {bytes : List UInt8}
    (h : flat.readBytes address count = some bytes) : bytes.length = count := by
  unfold readBytes at h
  split at h
  · injection h with h
    subst h
    simp
  · simp at h

theorem readBytes_eq_none {flat : Flat} {address count offset : Nat} (hlt : offset < count)
    (hr : flat.readableAt (address + offset) = false) :
    flat.readBytes address count = Option.none := by
  unfold readBytes readableRange
  rw [all_range_eq_false (p := fun i => flat.readableAt (address + i)) hlt hr]
  rfl

theorem readBytes_isSome {flat : Flat} {address count : Nat}
    (h : flat.readableRange address count = true) :
    (flat.readBytes address count).isSome = true := by
  unfold readBytes
  rw [if_pos h]
  rfl

theorem writeBytes_eq_none {flat : Flat} {address offset : Nat} {bytes : List UInt8}
    (hlt : offset < bytes.length) (hw : flat.writableAt (address + offset) = false) :
    flat.writeBytes address bytes = Option.none := by
  unfold writeBytes writableRange
  rw [all_range_eq_false (p := fun i => flat.writableAt (address + i)) hlt hw]
  rfl

theorem writeBytes_isSome {flat : Flat} {address : Nat} {bytes : List UInt8}
    (h : flat.writableRange address bytes.length = true) :
    (flat.writeBytes address bytes).isSome = true := by
  unfold writeBytes
  rw [if_pos h]
  rfl

theorem readBytes_writeBytes_self {flat next : Flat} {address : Nat} {bytes : List UInt8}
    (h : flat.writeBytes address bytes = some next)
    (hr : flat.readableRange address bytes.length = true) :
    next.readBytes address bytes.length = some bytes := by
  obtain ⟨hregions, _, hbytes⟩ := writeBytes_eq_some h
  have hnext : next.readableRange address bytes.length = true := by
    unfold readableRange readableAt
    simp only [regionAt_congr hregions]
    exact hr
  unfold readBytes
  rw [if_pos hnext]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i _ hi
    rw [List.getElem_map, List.getElem_range, hbytes]
    unfold writeAt
    rw [dif_pos (show address ≤ address + i ∧ address + i < address + bytes.length by omega)]
    simp only [Nat.add_sub_cancel_left]

theorem readBytes_writeBytes_of_disjoint {flat next : Flat} {address : Nat} {bytes : List UInt8}
    {query count : Nat} (h : flat.writeBytes address bytes = some next)
    (hd : AddressRangesDisjoint address bytes.length query count) :
    next.readBytes query count = flat.readBytes query count := by
  obtain ⟨hregions, _, hbytes⟩ := writeBytes_eq_some h
  have hrange : next.readableRange query count = flat.readableRange query count := by
    unfold readableRange readableAt
    simp only [regionAt_congr hregions]
  unfold readBytes
  rw [hrange]
  split
  · congr 1
    apply List.map_congr_left
    intro i hi
    have hlt : i < count := List.mem_range.mp hi
    rw [hbytes]
    unfold writeAt
    rw [dif_neg (show ¬ (address ≤ query + i ∧ query + i < address + bytes.length) by
      rcases hd with hd | hd <;> omega)]
  · rfl

theorem writeAt_comm (base : Nat → UInt8) (baseA : Nat) (bytesA : List UInt8) (baseB : Nat)
    (bytesB : List UInt8)
    (hd : AddressRangesDisjoint baseA bytesA.length baseB bytesB.length) :
    writeAt (writeAt base baseA bytesA) baseB bytesB =
      writeAt (writeAt base baseB bytesB) baseA bytesA := by
  funext query
  by_cases h1 : baseA ≤ query ∧ query < baseA + bytesA.length <;>
    by_cases h2 : baseB ≤ query ∧ query < baseB + bytesB.length
  · exact absurd hd (by rcases hd with hd | hd <;> omega)
  · simp only [writeAt, dif_neg h2, dif_pos h1]
  · simp only [writeAt, dif_pos h2, dif_neg h1]
  · simp only [writeAt, dif_neg h1, dif_neg h2]

theorem writeBytes_eq_of_writable {flat : Flat} {address : Nat} {bytes : List UInt8}
    (h : flat.writableRange address bytes.length = true) :
    flat.writeBytes address bytes =
      some { flat with bytes := writeAt flat.bytes address bytes } := by
  unfold writeBytes
  rw [if_pos h]

theorem writeBytes_eq_none_of_unwritable {flat : Flat} {address : Nat} {bytes : List UInt8}
    (h : ¬ (flat.writableRange address bytes.length = true)) :
    flat.writeBytes address bytes = Option.none := by
  unfold writeBytes
  rw [if_neg h]

theorem writeBytes_comm (flat : Flat) (baseA : Nat) (bytesA : List UInt8) (baseB : Nat)
    (bytesB : List UInt8)
    (hd : AddressRangesDisjoint baseA bytesA.length baseB bytesB.length) :
    ((flat.writeBytes baseA bytesA).bind fun next => next.writeBytes baseB bytesB) =
      ((flat.writeBytes baseB bytesB).bind fun next => next.writeBytes baseA bytesA) := by
  by_cases hA : flat.writableRange baseA bytesA.length = true <;>
    by_cases hB : flat.writableRange baseB bytesB.length = true
  · rw [writeBytes_eq_of_writable hA, writeBytes_eq_of_writable hB, Option.bind_some,
      Option.bind_some,
      writeBytes_eq_of_writable (flat := { flat with bytes := writeAt flat.bytes baseA bytesA })
        (address := baseB) (bytes := bytesB) hB,
      writeBytes_eq_of_writable (flat := { flat with bytes := writeAt flat.bytes baseB bytesB })
        (address := baseA) (bytes := bytesA) hA]
    simp only [Option.some.injEq, Flat.mk.injEq, and_true]
    exact writeAt_comm flat.bytes baseA bytesA baseB bytesB hd
  · rw [writeBytes_eq_of_writable hA, writeBytes_eq_none_of_unwritable hB, Option.bind_some,
      Option.bind_none,
      writeBytes_eq_none_of_unwritable
        (flat := { flat with bytes := writeAt flat.bytes baseA bytesA })
        (address := baseB) (bytes := bytesB) hB]
  · rw [writeBytes_eq_of_writable hB, writeBytes_eq_none_of_unwritable hA, Option.bind_some,
      Option.bind_none,
      writeBytes_eq_none_of_unwritable
        (flat := { flat with bytes := writeAt flat.bytes baseB bytesB })
        (address := baseA) (bytes := bytesA) hA]
  · rw [writeBytes_eq_none_of_unwritable hA, writeBytes_eq_none_of_unwritable hB,
      Option.bind_none, Option.bind_none]

theorem readableAt_writeBytes {flat next : Flat} {address : Nat} {bytes : List UInt8}
    (h : flat.writeBytes address bytes = some next) (query : Nat) :
    next.readableAt query = flat.readableAt query := by
  unfold readableAt
  rw [regionAt_congr (writeBytes_eq_some h).1 query]

theorem writableAt_writeBytes {flat next : Flat} {address : Nat} {bytes : List UInt8}
    (h : flat.writeBytes address bytes = some next) (query : Nat) :
    next.writableAt query = flat.writableAt query := by
  unfold writableAt
  rw [regionAt_congr (writeBytes_eq_some h).1 query]

theorem executableAt_writeBytes {flat next : Flat} {address : Nat} {bytes : List UInt8}
    (h : flat.writeBytes address bytes = some next) (query : Nat) :
    next.executableAt query = flat.executableAt query := by
  unfold executableAt
  rw [regionAt_congr (writeBytes_eq_some h).1 query]

theorem deviceAt_writeBytes {flat next : Flat} {address : Nat} {bytes : List UInt8}
    (h : flat.writeBytes address bytes = some next) (query : Nat) :
    next.deviceAt query = flat.deviceAt query := by
  unfold deviceAt
  rw [(writeBytes_eq_some h).2.1]

/-- The region search over a loaded plan: it finds the section that covers the
address if there is one, and otherwise falls through to the stack. This is the
one induction the load laws need. -/
theorem find?_sectionRegions (secs : List Grass.Target.Section) (address : Nat)
    (rest : List Region) :
    (secs.map sectionRegion ++ rest).find? (fun region => region.covers address) =
      match secs.find? fun sec => sectionCovers sec address with
      | some sec => some (sectionRegion sec)
      | Option.none => rest.find? fun region => region.covers address := by
  induction secs with
  | nil => simp
  | cons sec tl ih =>
      by_cases hs : sectionCovers sec address = true
      · rw [List.map_cons, List.cons_append,
          List.find?_cons_of_pos (p := fun region => region.covers address)
            (a := sectionRegion sec) hs,
          List.find?_cons_of_pos (p := fun s => sectionCovers s address) (a := sec) hs]
      · rw [List.map_cons, List.cons_append,
          List.find?_cons_of_neg (p := fun region => region.covers address)
            (a := sectionRegion sec) hs,
          List.find?_cons_of_neg (p := fun s => sectionCovers s address) (a := sec) hs, ih]

theorem regionAt_load_of_section {plan : LoadPlan} {address : Nat}
    {sec : Grass.Target.Section} (h : plan.sectionAt? address = some sec) :
    (load plan).regionAt address = some (sectionRegion sec) := by
  unfold regionAt load
  rw [find?_sectionRegions]
  unfold LoadPlan.sectionAt? at h
  rw [h]

theorem regionAt_load_of_unmapped {plan : LoadPlan} {address : Nat}
    (hsec : plan.sectionAt? address = Option.none) (hstack : plan.stackCovers address = false) :
    (load plan).regionAt address = Option.none := by
  unfold regionAt load
  rw [find?_sectionRegions]
  unfold LoadPlan.sectionAt? at hsec
  rw [hsec]
  have hstackRegion : ¬ ((stackRegion plan).covers address = true) := by
    unfold stackRegion Region.covers
    unfold LoadPlan.stackCovers at hstack
    rw [hstack]
    exact Bool.noConfusion
  rw [List.find?_cons_of_neg (p := fun region => region.covers address)
    (a := stackRegion plan) hstackRegion, List.find?_nil]

theorem readBytes_load {plan : LoadPlan} {address count : Nat} {bytes : List UInt8}
    (h : (load plan).readBytes address count = some bytes) :
    bytes = (List.range count).map fun offset => plan.byteAt (address + offset) := by
  unfold readBytes at h
  split at h
  · injection h with h
    exact h.symm
  · simp at h

theorem readableAt_load_of_unmapped {plan : LoadPlan} {address : Nat}
    (hsec : plan.sectionAt? address = Option.none) (hstack : plan.stackCovers address = false) :
    (load plan).readableAt address = false := by
  unfold readableAt
  rw [regionAt_load_of_unmapped hsec hstack]
  rfl

theorem readableAt_load_of_section {plan : LoadPlan} {address : Nat}
    {sec : Grass.Target.Section} (h : plan.sectionAt? address = some sec) :
    (load plan).readableAt address = sec.readable := by
  unfold readableAt
  rw [regionAt_load_of_section h]
  rfl

theorem executableAt_load_of_section {plan : LoadPlan} {address : Nat}
    {sec : Grass.Target.Section} (h : plan.sectionAt? address = some sec) :
    (load plan).executableAt address = sec.executable := by
  unfold executableAt
  rw [regionAt_load_of_section h]
  rfl

end Flat

/-- The flat memory the three ISA records carry today, as a `MachineMemory`. -/
def flat : MachineMemory where
  Mem := Flat
  readableAt := Flat.readableAt
  writableAt := Flat.writableAt
  executableAt := Flat.executableAt
  deviceAt := Flat.deviceAt
  readBytes := Flat.readBytes
  writeBytes := Flat.writeBytes
  load := Flat.load

/-- **The flat instance satisfies every law.** -/
theorem flat_laws : MachineMemory.Laws flat where
  readBytes_length := fun _ _ _ _ h => Flat.readBytes_length h
  readBytes_eq_none := fun _ _ _ _ hlt hr => Flat.readBytes_eq_none hlt hr
  readBytes_isSome := fun _ _ _ h => Flat.readBytes_isSome h
  writeBytes_eq_none := fun _ _ _ _ hlt hw => Flat.writeBytes_eq_none hlt hw
  writeBytes_isSome := fun _ _ _ h => Flat.writeBytes_isSome h
  readableAt_writeBytes := fun _ _ _ query _ h => Flat.readableAt_writeBytes h query
  writableAt_writeBytes := fun _ _ _ query _ h => Flat.writableAt_writeBytes h query
  executableAt_writeBytes := fun _ _ _ query _ h => Flat.executableAt_writeBytes h query
  deviceAt_writeBytes := fun _ _ _ query _ h => Flat.deviceAt_writeBytes h query
  readBytes_writeBytes_self := fun _ _ _ _ h hr => Flat.readBytes_writeBytes_self h hr
  readBytes_writeBytes_of_disjoint := fun _ _ _ _ _ _ h hd =>
    Flat.readBytes_writeBytes_of_disjoint h hd
  writeBytes_comm := fun m baseA bytesA baseB bytesB hd =>
    Flat.writeBytes_comm m baseA bytesA baseB bytesB hd
  readableAt_load_of_unmapped := fun _ _ hsec hstack =>
    Flat.readableAt_load_of_unmapped hsec hstack
  readableAt_load_of_section := fun _ _ _ h => Flat.readableAt_load_of_section h
  executableAt_load_of_section := fun _ _ _ h => Flat.executableAt_load_of_section h
  readBytes_load := fun _ _ _ _ h => Flat.readBytes_load h
  deviceAt_load := fun _ _ => rfl

/-! ### Non-vacuity

`MachineMemory.Laws` is satisfiable by a memory that refuses everything for
every law except the two `isSome` clauses, and those two are only as strong as
the loader that has to supply a readable region. These four closed facts are the
check that the flat instance is a memory a machine can actually run on: an
image byte reads back, an unmapped address does not, a read-only section refuses
a store, and the stack round-trips a write. -/

/-- One readable, executable, non-writable section at 16, a stack at 64, and a
device window at 128. -/
private def sampleSection : Grass.Target.Section :=
  { name := "sample", virtualAddress := 16, bytes := [1, 2, 3, 4], readable := true,
    writable := false, executable := true }

private def samplePlan : LoadPlan :=
  { sections := [sampleSection], stackBase := 64, stackSize := 8, staged := []
    devices := [{ base := 128, size := 4 }] }

/-- **A loaded section's bytes read back.** -/
theorem flat_reads_loaded_section :
    Flat.readBytes (Flat.load samplePlan) 16 4 = some [1, 2, 3, 4] := by decide

/-- **An address outside every section and the stack does not read.** -/
theorem flat_refuses_unmapped : Flat.readBytes (Flat.load samplePlan) 8 1 = Option.none := by
  decide

/-- **A read-only section refuses a store.** -/
theorem flat_refuses_readonly_write :
    Flat.writeBytes (Flat.load samplePlan) 16 [9] = Option.none := by decide

/-- **The stack round-trips a write.** -/
theorem flat_stack_round_trip :
    ((Flat.load samplePlan).writeBytes 64 [7]).bind (fun next => next.readBytes 64 1) =
      some [7] := by decide

/-! ## The provenance instance

The same interface, backed by `Grass.Memory.MemoryState`. A machine address is
resolved to an installed *view* — an address range paired with the `Provenance`
of the allocation it denotes — and the access then goes through
`MemoryState.resolveAccess?`, so liveness, epoch, address space, allocation
source, provenance nesting, the backing binding, and the whole-view bound are
all checked before a byte is read. The allocation's own `Permission` is the
rights gate, and a store commits through `MemoryState.writeResolved`, which
writes the allocation's backing at the resolved backing span.

### What is proved, and what is not

Proved below: `readBytes_length`, the three permission-stability laws and the
device-window law, `writeBytes_eq_none` and `readBytes_eq_none` at the address a
view is entered at, and the loader's device law.

Not proved, and the report beside this file says why: `readBytes_writeBytes_self`,
`readBytes_writeBytes_of_disjoint` and `writeBytes_comm` all need a
`ResolvedAccess` transported across a `writeResolved`, which is
`MemoryState.ResolvedAccess.afterWrite`; the byte-level content then comes from
`cellAt?_writeResolved_of_covers` and `cellAt?_writeResolved_of_untouched`, and
commutation from `writeResolved_comm`. Every ingredient exists in
`Grass/Memory/State.lean`. What is missing is the bridge from a *machine
address* range to the allocation-local `ByteRange` those lemmas are stated over,
and the two positive laws (`readBytes_isSome`, `writeBytes_isSome`) additionally
need the initialization side condition discharged. `Mapped` is therefore
published as operations plus the laws below, not as a `MachineMemory.Laws`
instance, because a `Laws` value cannot be honest until all of them close.
-/

/-- A machine-address base paired with the provenance presented by accesses.
`MappedRegion.covers` uses `provenance.extent.size` as the view's length.
The record alone carries no allocation-validity proof; `Mapped.readBytes` and
`Mapped.writeBytes` check the provenance and requested range through
`MemoryState.resolveAccess?` before accessing the backing. -/
structure MappedRegion where
  /-- The lowest machine address the view occupies. -/
  base : Nat
  /-- The provenance the view's accesses present. -/
  provenance : Provenance
deriving Repr

/-- Whether a machine address falls inside the view. -/
def MappedRegion.covers (region : MappedRegion) (address : Nat) : Bool :=
  decide (region.base ≤ address ∧ address < region.base + region.provenance.extent.size)

/-- The allocation-local offset a machine address denotes in this view. -/
def MappedRegion.localOffset (region : MappedRegion) (address : Nat) : Nat :=
  region.provenance.extent.start + (address - region.base)

/-- Provenance-checked memory: the model's own state, the address views
installed over it, and the device windows. -/
structure Mapped where
  /-- The memory model's state: allocations, backings, and grants. -/
  state : MemoryState
  /-- The installed address views, searched in order. -/
  regions : List MappedRegion
  /-- The device windows. -/
  devices : List DeviceWindow

namespace Mapped

/-- Nothing mapped: every access is refused. -/
def unmapped : Mapped := { state := .empty, regions := [], devices := [] }

/-- The view containing an address, if any. -/
def regionAt (mapped : Mapped) (address : Nat) : Option MappedRegion :=
  mapped.regions.find? fun region => region.covers address

/-- The allocation record a machine address reaches, if any. -/
def recordAt (mapped : Mapped) (address : Nat) : Option AllocationRecord :=
  (mapped.regionAt address).bind fun region =>
    mapped.state.allocations.lookup region.provenance.root

/-- Whether an address may be read: its allocation must be live and its
permission must carry read. A dead allocation authorizes nothing, whatever view
still names it. -/
def readableAt (mapped : Mapped) (address : Nat) : Bool :=
  match mapped.recordAt address with
  | some record => record.live && record.permission.read
  | Option.none => false

/-- Whether an address may be written. -/
def writableAt (mapped : Mapped) (address : Nat) : Bool :=
  match mapped.recordAt address with
  | some record => record.live && record.permission.write
  | Option.none => false

/-- Whether an address may be executed. -/
def executableAt (mapped : Mapped) (address : Nat) : Bool :=
  match mapped.recordAt address with
  | some record => record.live && record.permission.execute
  | Option.none => false

/-- Whether an address lies in a device window. -/
def deviceAt (mapped : Mapped) (address : Nat) : Bool :=
  mapped.devices.any fun window => window.covers address

/--
Read through the model.

The whole range is resolved once, as `docs/MEMORY_MODEL.md` §1 asks: one access,
one provenance, one checked backing span. Reads are refused unless the range is
initialized, which is §4's "initialization is tracked at the granularity
required to justify every read" — the flat ISAs cannot express that demand at
all, because a flat byte is always a value.

The `getD 0` is unreachable: `RangeInitialized` makes every cell of the resolved
span `some`. Proving it unreachable is a lemma
(`ResolvedAccess.byteAt?_isSome_of_rangeInitialized`) that does not exist yet.
-/
def readBytes (mapped : Mapped) (address count : Nat) : Option (List UInt8) :=
  match mapped.regionAt address with
  | Option.none => Option.none
  | some region =>
      match mapped.state.resolveAccess? region.provenance
          ⟨region.localOffset address, count⟩ with
      | .error _ => Option.none
      | .ok access =>
          if access.allocation.permission.read = true ∧ access.RangeInitialized then
            some ((List.range count).map fun offset =>
              UInt8.ofBitVec ((access.byteAt? (region.localOffset address + offset)).getD 0))
          else Option.none

/-- Write through the model: resolve once, check the allocation's write right,
and commit to its backing with `writeResolved`, which initializes exactly the
bytes it completes. -/
def writeBytes (mapped : Mapped) (address : Nat) (bytes : List UInt8) : Option Mapped :=
  match mapped.regionAt address with
  | Option.none => Option.none
  | some region =>
      match mapped.state.resolveAccess? region.provenance
          ⟨region.localOffset address, bytes.length⟩ with
      | .error _ => Option.none
      | .ok access =>
          if access.allocation.permission.write = true then
            some { mapped with
              state := mapped.state.writeResolved access (bytes.map UInt8.toBitVec) true
                (by simp) }
          else Option.none

/-! ### Installation

An image section, a staged block, and the stack each become one allocation with
a fresh identity, a fresh epoch, a fresh backing, and the model's own
`imageMapping` or `stack` source. This is the ledger the flat ISAs do not have:
after a load, `MemoryState.allocations` says which bytes belong to which
allocation and what each one permits.
-/

/-- The identity supplies and the state an installation is building. -/
structure Install where
  /-- The state built so far. -/
  state : MemoryState
  /-- The views installed so far. -/
  regions : List MappedRegion
  /-- Unissued allocation identities. -/
  allocs : Grass.Core.FreshSupply AllocTag
  /-- Unissued backing identities. -/
  storages : Grass.Core.FreshSupply StorageTag
  /-- Unissued epochs. -/
  epochs : Grass.Core.FreshSupply EpochTag

/-- The supplies before anything is installed. -/
def Install.start : Install :=
  { state := .empty, regions := [], allocs := .initial, storages := .initial,
    epochs := .initial }

/-- Install one placed byte block as a fresh allocation over a fresh backing. -/
def Install.one (acc : Install) (base : Nat) (bytes : List UInt8) (permission : Permission)
    (source : AllocationSourceId) : Option Install :=
  let (allocId, allocs) := acc.allocs.fresh
  let (storageId, storages) := acc.storages.fresh
  let (epochId, epochs) := acc.epochs.fresh
  let extent : ByteRange := ⟨0, bytes.length⟩
  let backing : BackingRecord :=
    { capacity := bytes.length
      bytes := ByteStore.empty.write 0 (bytes.map UInt8.toBitVec) true }
  match acc.state.installBacking? storageId backing with
  | Option.none => Option.none
  | some withBacking =>
      let record : AllocationRecord :=
        { extent := extent, epoch := epochId, space := .cpuVirtual, source := source,
          owners := [], permission := permission, live := true, backing := storageId,
          origin := 0, base := some (BitVec.ofNat 64 base) }
      match withBacking.allocate? allocId record with
      | Option.none => Option.none
      | some next =>
          some { state := next
                 regions := acc.regions ++
                   [{ base := base
                      provenance :=
                        { space := .cpuVirtual, root := allocId, epoch := epochId,
                          source := source, rootExtent := extent, path := [] } }]
                 allocs := allocs, storages := storages, epochs := epochs }

/-- Install a whole plan, or refuse it. -/
def install? (plan : LoadPlan) : Option Install := do
  let afterSections ← plan.sections.foldlM (fun acc sec =>
    acc.one sec.virtualAddress sec.bytes
      { read := sec.readable, write := sec.writable, execute := sec.executable }
      AllocationSourceId.imageMapping) Install.start
  let afterStaged ← plan.staged.foldlM (fun acc region =>
    acc.one region.1 region.2 Permission.readWrite AllocationSourceId.imageMapping)
    afterSections
  afterStaged.one plan.stackBase (List.replicate plan.stackSize 0)
    Permission.readWrite AllocationSourceId.stack

/-- Install a plan, refusing every access if the model refuses the plan. Failing
closed is the only safe reading: a refused installation must not become a
machine that runs. The device windows are the plan's either way, because
routing an MMIO access to the platform is not an authority the model grants. -/
def load (plan : LoadPlan) : Mapped :=
  match install? plan with
  | some acc => { state := acc.state, regions := acc.regions, devices := plan.devices }
  | Option.none => { unmapped with devices := plan.devices }

/-! ### Laws proved for this instance -/

theorem readBytes_length {mapped : Mapped} {address count : Nat} {bytes : List UInt8}
    (h : mapped.readBytes address count = some bytes) : bytes.length = count := by
  unfold readBytes at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · injection h with h
        subst h
        simp
      · simp at h

/-- What a successful write produced: the view map, the device map, the
allocation table and every backing capacity are untouched. This is the whole
content of the permission-stability laws, because `readableAt` reads exactly
`regions` and `allocations`. -/
theorem writeBytes_eq_some {mapped next : Mapped} {address : Nat} {bytes : List UInt8}
    (h : mapped.writeBytes address bytes = some next) :
    next.regions = mapped.regions ∧ next.devices = mapped.devices ∧
      next.state.allocations = mapped.state.allocations := by
  unfold writeBytes at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · injection h with h
        subst h
        exact ⟨rfl, rfl, rfl⟩
      · simp at h

theorem recordAt_congr {mapped next : Mapped} (hregions : next.regions = mapped.regions)
    (hallocations : next.state.allocations = mapped.state.allocations) (address : Nat) :
    next.recordAt address = mapped.recordAt address := by
  unfold recordAt regionAt
  rw [hregions, hallocations]

theorem readableAt_writeBytes {mapped next : Mapped} {address : Nat} {bytes : List UInt8}
    (h : mapped.writeBytes address bytes = some next) (query : Nat) :
    next.readableAt query = mapped.readableAt query := by
  obtain ⟨hregions, _, hallocations⟩ := writeBytes_eq_some h
  unfold readableAt
  rw [recordAt_congr hregions hallocations query]

theorem writableAt_writeBytes {mapped next : Mapped} {address : Nat} {bytes : List UInt8}
    (h : mapped.writeBytes address bytes = some next) (query : Nat) :
    next.writableAt query = mapped.writableAt query := by
  obtain ⟨hregions, _, hallocations⟩ := writeBytes_eq_some h
  unfold writableAt
  rw [recordAt_congr hregions hallocations query]

theorem executableAt_writeBytes {mapped next : Mapped} {address : Nat} {bytes : List UInt8}
    (h : mapped.writeBytes address bytes = some next) (query : Nat) :
    next.executableAt query = mapped.executableAt query := by
  obtain ⟨hregions, _, hallocations⟩ := writeBytes_eq_some h
  unfold executableAt
  rw [recordAt_congr hregions hallocations query]

theorem deviceAt_writeBytes {mapped next : Mapped} {address : Nat} {bytes : List UInt8}
    (h : mapped.writeBytes address bytes = some next) (query : Nat) :
    next.deviceAt query = mapped.deviceAt query := by
  obtain ⟨_, hdevices, _⟩ := writeBytes_eq_some h
  unfold deviceAt
  rw [hdevices]

/-- The record a resolution found is the record the permission gate reads: the
resolution's own `allocationLookup` is a lookup of the same allocation the view
names. This is what makes the two denial laws below about the *same* rights the
model checked, rather than about a second copy of them. -/
theorem recordAt_eq_of_resolved {mapped : Mapped} {address : Nat}
    {region : MappedRegion} {requested : ByteRange}
    (hregion : mapped.regionAt address = some region)
    (access : mapped.state.ResolvedAccess region.provenance requested) :
    mapped.recordAt address = some access.allocation := by
  unfold recordAt
  rw [hregion]
  exact access.allocationLookup

/-- **A write the permission gate denies is `none`.** -/
theorem writeBytes_eq_none {mapped : Mapped} {address : Nat} {bytes : List UInt8}
    (hw : mapped.writableAt address = false) :
    mapped.writeBytes address bytes = Option.none := by
  unfold writeBytes
  split
  · rfl
  · rename_i region hregion
    split
    · rfl
    · rename_i access _
      rw [if_neg]
      intro hperm
      have hrecord : mapped.recordAt address = some access.allocation :=
        recordAt_eq_of_resolved hregion access
      unfold writableAt at hw
      rw [hrecord] at hw
      simp [access.allocationLive, hperm] at hw

/-- **A read the permission gate denies is `none`.** -/
theorem readBytes_eq_none {mapped : Mapped} {address count : Nat}
    (hr : mapped.readableAt address = false) :
    mapped.readBytes address count = Option.none := by
  unfold readBytes
  split
  · rfl
  · rename_i region hregion
    split
    · rfl
    · rename_i access _
      rw [if_neg]
      intro hgate
      have hrecord : mapped.recordAt address = some access.allocation :=
        recordAt_eq_of_resolved hregion access
      unfold readableAt at hr
      rw [hrecord] at hr
      simp [access.allocationLive, hgate.1] at hr

/-- **An address no view covers is not readable, whatever bytes the model
holds.** The provenance instance's answer to "out of bounds is `none`". -/
theorem readableAt_eq_false_of_unmapped {mapped : Mapped} {address : Nat}
    (h : mapped.regionAt address = Option.none) : mapped.readableAt address = false := by
  unfold readableAt recordAt
  rw [h]
  rfl

/-! ### Non-vacuity

This instance fails closed when the model refuses a plan, so every denial law
above would also hold of an installation that always refuses. These are the
check that it does not: the same sample plan installs as allocations with
`imageMapping` and `stack` sources, and its image bytes read back *through*
provenance resolution, the allocation's rights, and the initialization demand
that a flat memory cannot even express. -/

theorem mapped_installs : (install? samplePlan).isSome = true := by decide

/-- **A loaded section's bytes read back through the provenance model.** -/
theorem mapped_reads_loaded_section :
    readBytes (load samplePlan) 16 4 = some [1, 2, 3, 4] := by decide

/-- **A read-only section's allocation refuses a store.** -/
theorem mapped_refuses_readonly_write :
    writeBytes (load samplePlan) 16 [9] = Option.none := by decide

/-- **An address no view covers does not read.** -/
theorem mapped_refuses_unmapped : readBytes (load samplePlan) 8 1 = Option.none := by decide

theorem deviceAt_load (plan : LoadPlan) (address : Nat) :
    (load plan).deviceAt address = plan.devices.any fun window => window.covers address := by
  unfold load deviceAt
  split <;> rfl

end Mapped

/-- The provenance-backed memory as a `MachineMemory`. It is deliberately *not*
accompanied by a `MachineMemory.Laws` value: see the module comment above
`MappedRegion` for the three laws that remain open. -/
def mapped : MachineMemory where
  Mem := Mapped
  readableAt := Mapped.readableAt
  writableAt := Mapped.writableAt
  executableAt := Mapped.executableAt
  deviceAt := Mapped.deviceAt
  readBytes := Mapped.readBytes
  writeBytes := Mapped.writeBytes
  load := Mapped.load

end Grass.Memory
