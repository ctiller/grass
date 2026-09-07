import Grass.Unsafe.Construct

/-!
# Tainted raw hierarchy emission

`emitRaw` applies an explicitly supplied instruction encoder to the exact
located expansion of a fragment source. The result retains each structural
origin, its consecutive byte offset, and a mandatory taint ledger. This unsafe
adapter provides no decoding, semantic, relocation, or artifact certificate.
-/

namespace Grass.Unsafe

open Grass.Construct.Fragment

universe u

variable {Instruction : Type u}

/-- Unverified instruction-to-byte function supplied at the unsafe boundary. -/
structure RawEncoder (Instruction : Type u) where
  encode : Instruction → List UInt8

/-- One raw instruction encoding with its exact source location and byte offset. -/
structure RawEncodedInstruction (Instruction : Type u) where
  located : LocatedInstruction Instruction
  offset : Nat
  bytes : List UInt8
deriving Repr, DecidableEq

namespace RawEncodedInstruction

/-- First byte offset immediately after this raw instruction encoding. -/
def endOffset (item : RawEncodedInstruction Instruction) : Nat :=
  item.offset + item.bytes.length

end RawEncodedInstruction

/-- Exact consecutive-offset invariant for a raw instruction sequence. -/
def ConsecutiveOffsets : Nat → List (RawEncodedInstruction Instruction) → Prop
  | _, [] => True
  | expected, item :: rest =>
      item.offset = expected ∧ ConsecutiveOffsets item.endOffset rest

private def encodeLocatedFrom (encoder : RawEncoder Instruction) :
    Nat → List (LocatedInstruction Instruction) →
      List (RawEncodedInstruction Instruction)
  | _, [] => []
  | offset, located :: rest =>
      let bytes := encoder.encode located.instruction
      ⟨located, offset, bytes⟩ ::
        encodeLocatedFrom encoder (offset + bytes.length) rest

private theorem encodeLocatedFrom_locations
    (encoder : RawEncoder Instruction) (offset : Nat)
    (located : List (LocatedInstruction Instruction)) :
    (encodeLocatedFrom encoder offset located).map
      RawEncodedInstruction.located = located := by
  induction located generalizing offset with
  | nil => rfl
  | cons head rest ih =>
      simp [encodeLocatedFrom, ih]

private theorem encodeLocatedFrom_bytes
    (encoder : RawEncoder Instruction) (offset : Nat)
    (located : List (LocatedInstruction Instruction)) :
    (encodeLocatedFrom encoder offset located).flatMap
      RawEncodedInstruction.bytes =
    located.flatMap fun item => encoder.encode item.instruction := by
  induction located generalizing offset with
  | nil => rfl
  | cons head rest ih =>
      simp [encodeLocatedFrom, ih]

private theorem encodeLocatedFrom_offsets
    (encoder : RawEncoder Instruction) (offset : Nat)
    (located : List (LocatedInstruction Instruction)) :
    ConsecutiveOffsets offset (encodeLocatedFrom encoder offset located) := by
  induction located generalizing offset with
  | nil => trivial
  | cons head rest ih =>
      exact ⟨rfl, ih (offset + (encoder.encode head.instruction).length)⟩

/-- Raw emitted bytes with complete per-instruction source and taint metadata. -/
structure RawEmission (Instruction : Type u) where
  source : Source Instruction
  items : List (RawEncodedInstruction Instruction)
  primaryTaint : Taint
  additionalTaints : List Taint := []

namespace RawEmission

/-- Raw bytes in exact instruction and encoder order. -/
def bytes (emission : RawEmission Instruction) : List UInt8 :=
  emission.items.flatMap RawEncodedInstruction.bytes

/-- Total serialized byte length of the raw stream. -/
def byteLength (emission : RawEmission Instruction) : Nat :=
  emission.bytes.length

/-- Every taint in stable review order, beginning with the mandatory reason. -/
def taints (emission : RawEmission Instruction) : List Taint :=
  emission.primaryTaint :: emission.additionalTaints

/-- The raw emission taint ledger is necessarily nonempty. -/
theorem taints_ne_nil (emission : RawEmission Instruction) :
    emission.taints ≠ [] := by
  simp [taints]

end RawEmission

/-- Emit a hierarchical source through one explicitly unverified encoder. -/
def emitRaw (source : Source Instruction) (encoder : RawEncoder Instruction)
    (primaryTaint : Taint) (additionalTaints : List Taint := []) :
    RawEmission Instruction where
  source := source
  items := encodeLocatedFrom encoder 0 source.expandLocated
  primaryTaint := primaryTaint
  additionalTaints := additionalTaints

namespace emitRaw

/-- Emission retains every located instruction in exact structural order. -/
theorem locationsExact (source : Source Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitRaw source encoder primaryTaint additionalTaints).items.map
      RawEncodedInstruction.located = source.expandLocated :=
  encodeLocatedFrom_locations encoder 0 source.expandLocated

/-- Projected emitted instructions equal the exact source expansion. -/
theorem instructionsExact (source : Source Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitRaw source encoder primaryTaint additionalTaints).items.map
      (fun item => item.located.instruction) = source.expand := by
  calc
    _ = source.expandLocated.map LocatedInstruction.instruction := by
      simpa [List.map_map, Function.comp_def] using
        congrArg (List.map LocatedInstruction.instruction)
          (locationsExact source encoder primaryTaint additionalTaints)
    _ = source.expand := (Source.expand_eq_map_located source).symm

/-- Raw bytes are exactly the supplied encoder applied in located source order. -/
theorem bytesExact (source : Source Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitRaw source encoder primaryTaint additionalTaints).bytes =
      source.expandLocated.flatMap fun item => encoder.encode item.instruction :=
  encodeLocatedFrom_bytes encoder 0 source.expandLocated

/-- Every emitted item begins exactly where its predecessor ends. -/
theorem offsetsExact (source : Source Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    ConsecutiveOffsets 0
      (emitRaw source encoder primaryTaint additionalTaints).items :=
  encodeLocatedFrom_offsets encoder 0 source.expandLocated

/-- `emitRaw.taintsExact` preserves the mandatory and additional taint sequence. -/
theorem taintsExact (source : Source Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitRaw source encoder primaryTaint additionalTaints).taints =
      primaryTaint :: additionalTaints := rfl

end emitRaw

end Grass.Unsafe
