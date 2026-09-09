import Grass.Memory.ByteStore
import Grass.Memory.Coordinates

/-!
# Authoritative backing storage

Allocation records are views. Bytes and their initialization state live once,
in a backing record keyed by `StorageId`. Capacity is stable metadata of that
backing and is deliberately independent of the cells currently represented by
`ByteStore`.
-/

namespace Grass.Memory

open Grass.Std.Logical

/-- One backing identity's stable capacity and authoritative bytes. -/
structure BackingRecord where
  capacity : Nat
  bytes : ByteStore
deriving DecidableEq, Repr

namespace BackingRecord

/-- Read a cell in backing coordinates. -/
def cellAt? (record : BackingRecord) (offset : Nat) : Option (Byte × Bool) :=
  record.bytes.cellAt? offset

/-- Read a byte in backing coordinates. -/
def byteAt? (record : BackingRecord) (offset : Nat) : Option Byte :=
  record.bytes.byteAt? offset

/-- Update bytes without changing the backing's capacity. -/
def write (record : BackingRecord) (start : Nat) (bytes : ByteSeq)
    (initializes : Bool) : BackingRecord :=
  { record with bytes := record.bytes.write start bytes initializes }

@[simp] theorem capacity_write (record : BackingRecord) (start : Nat)
    (bytes : ByteSeq) (initializes : Bool) :
    (record.write start bytes initializes).capacity = record.capacity := rfl

end BackingRecord

end Grass.Memory
