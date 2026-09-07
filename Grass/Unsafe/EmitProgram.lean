import Grass.Construct.Source.ConstructionLower
import Grass.Unsafe.Emit

/-!
# Tainted raw lowered-program emission

`emitRawProgram` extends raw instruction encoding to `LoweredProgram`, retaining
the exact containing block and `SourceOrigin` of every item. The
`emitVerifiedConstructionRaw` bridge accepts unified verified construction
input and exposes exact CFG and pre-alpha instruction theorems, but the encoder
and emitted bytes remain explicitly tainted and uncertified.
-/

namespace Grass.Unsafe

open Grass.CFG Grass.Construct.Fragment Grass.Construct.Source

universe u v w x y

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}

/-- One raw encoding of an exact lowered instruction and its byte offset. -/
structure RawProgramEncodedInstruction (Instruction : Type w) where
  lowered : LoweredInstruction Instruction
  offset : Nat
  bytes : List UInt8
deriving Repr, DecidableEq

namespace RawProgramEncodedInstruction

/-- First byte offset immediately after this lowered instruction encoding. -/
def endOffset (item : RawProgramEncodedInstruction Instruction) : Nat :=
  item.offset + item.bytes.length

end RawProgramEncodedInstruction

/-- Exact consecutive-offset invariant for a raw lowered-program sequence. -/
def ConsecutiveProgramOffsets :
    Nat → List (RawProgramEncodedInstruction Instruction) → Prop
  | _, [] => True
  | expected, item :: rest =>
      item.offset = expected ∧
        ConsecutiveProgramOffsets item.endOffset rest

private def encodeProgramFrom (encoder : RawEncoder Instruction) :
    Nat → List (LoweredInstruction Instruction) →
      List (RawProgramEncodedInstruction Instruction)
  | _, [] => []
  | offset, lowered :: rest =>
      let bytes := encoder.encode lowered.instruction
      ⟨lowered, offset, bytes⟩ ::
        encodeProgramFrom encoder (offset + bytes.length) rest

private theorem encodeProgramFrom_lowered
    (encoder : RawEncoder Instruction) (offset : Nat)
    (items : List (LoweredInstruction Instruction)) :
    (encodeProgramFrom encoder offset items).map
      RawProgramEncodedInstruction.lowered = items := by
  induction items generalizing offset with
  | nil => rfl
  | cons head rest ih => simp [encodeProgramFrom, ih]

private theorem encodeProgramFrom_bytes
    (encoder : RawEncoder Instruction) (offset : Nat)
    (items : List (LoweredInstruction Instruction)) :
    (encodeProgramFrom encoder offset items).flatMap
      RawProgramEncodedInstruction.bytes =
    items.flatMap fun item => encoder.encode item.instruction := by
  induction items generalizing offset with
  | nil => rfl
  | cons head rest ih => simp [encodeProgramFrom, ih]

private theorem encodeProgramFrom_offsets
    (encoder : RawEncoder Instruction) (offset : Nat)
    (items : List (LoweredInstruction Instruction)) :
    ConsecutiveProgramOffsets offset (encodeProgramFrom encoder offset items) := by
  induction items generalizing offset with
  | nil => trivial
  | cons head rest ih =>
      exact ⟨rfl, ih (offset + (encoder.encode head.instruction).length)⟩

/-- Tainted raw bytes retaining the exact lowered CFG and source locations. -/
structure RawProgramEmission (State : Type u) (Terminal : Type v)
    (Instruction : Type w) where
  graph : Graph State Terminal
  items : List (RawProgramEncodedInstruction Instruction)
  primaryTaint : Taint
  additionalTaints : List Taint := []

namespace RawProgramEmission

/-- Raw bytes in exact lowered-instruction and encoder order. -/
def bytes (emission : RawProgramEmission State Terminal Instruction) : List UInt8 :=
  emission.items.flatMap RawProgramEncodedInstruction.bytes

/-- Total serialized byte length of the lowered raw stream. -/
def byteLength (emission : RawProgramEmission State Terminal Instruction) : Nat :=
  emission.bytes.length

/-- Every taint in stable review order, beginning with the mandatory reason. -/
def taints (emission : RawProgramEmission State Terminal Instruction) : List Taint :=
  emission.primaryTaint :: emission.additionalTaints

/-- The raw lowered-program taint ledger is necessarily nonempty. -/
theorem taints_ne_nil (emission : RawProgramEmission State Terminal Instruction) :
    emission.taints ≠ [] := by
  simp [taints]

end RawProgramEmission

/-- Emit one lowered program through an explicitly unverified encoder. -/
def emitRawProgram (program : LoweredProgram State Terminal Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    RawProgramEmission State Terminal Instruction where
  graph := program.graph
  items := encodeProgramFrom encoder 0 program.items
  primaryTaint := primaryTaint
  additionalTaints := additionalTaints

namespace emitRawProgram

/-- `emitRawProgram.graphExact` retains the exact lowered CFG. -/
@[simp] theorem graphExact (program : LoweredProgram State Terminal Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitRawProgram program encoder primaryTaint additionalTaints).graph =
      program.graph := rfl

/-- Every raw item retains the exact corresponding lowered instruction. -/
theorem loweredExact (program : LoweredProgram State Terminal Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitRawProgram program encoder primaryTaint additionalTaints).items.map
      RawProgramEncodedInstruction.lowered = program.items :=
  encodeProgramFrom_lowered encoder 0 program.items

/-- Projected raw instructions equal the lowered instruction sequence. -/
theorem instructionsExact (program : LoweredProgram State Terminal Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitRawProgram program encoder primaryTaint additionalTaints).items.map
      (fun item => item.lowered.instruction) =
      program.items.map LoweredInstruction.instruction := by
  simpa [List.map_map, Function.comp_def] using
    congrArg (List.map LoweredInstruction.instruction)
      (loweredExact program encoder primaryTaint additionalTaints)

/-- Raw bytes equal the supplied encoder applied in lowered-program order. -/
theorem bytesExact (program : LoweredProgram State Terminal Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitRawProgram program encoder primaryTaint additionalTaints).bytes =
      program.items.flatMap fun item => encoder.encode item.instruction :=
  encodeProgramFrom_bytes encoder 0 program.items

/-- Every program item begins exactly where its predecessor ends. -/
theorem offsetsExact (program : LoweredProgram State Terminal Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    ConsecutiveProgramOffsets 0
      (emitRawProgram program encoder primaryTaint additionalTaints).items :=
  encodeProgramFrom_offsets encoder 0 program.items

/-- `emitRawProgram.taintsExact` preserves the exact ordered taint sequence. -/
theorem taintsExact (program : LoweredProgram State Terminal Instruction)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitRawProgram program encoder primaryTaint additionalTaints).taints =
      primaryTaint :: additionalTaints := rfl

end emitRawProgram

/-- Emit a unified verified construction through an explicitly raw encoder. -/
def emitVerifiedConstructionRaw
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    [DecidableEq Terminal]
    {source : PreAlphaConstructionSource State Terminal Instruction Annotation
      Effect semantics effectModel}
    {model : LabelAlphaModel}
    (checked : VerifiedConstructionElaborated source model)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    RawProgramEmission State Terminal Instruction :=
  emitRawProgram checked.lower encoder primaryTaint additionalTaints

namespace emitVerifiedConstructionRaw

/-- Verified raw emission retains the exact normalized CFG. -/
@[simp] theorem graphExact
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    [DecidableEq Terminal]
    {source : PreAlphaConstructionSource State Terminal Instruction Annotation
      Effect semantics effectModel}
    {model : LabelAlphaModel}
    (checked : VerifiedConstructionElaborated source model)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitVerifiedConstructionRaw checked encoder primaryTaint
      additionalTaints).graph =
      (source.authored.alphaNormalize model).toGraph :=
  by
    change checked.lower.graph = (source.authored.alphaNormalize model).toGraph
    exact checked.lower_graph

/-- Verified raw emission projects exactly to original pre-alpha instructions. -/
theorem instructionsExact
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    [DecidableEq Terminal]
    {source : PreAlphaConstructionSource State Terminal Instruction Annotation
      Effect semantics effectModel}
    {model : LabelAlphaModel}
    (checked : VerifiedConstructionElaborated source model)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitVerifiedConstructionRaw checked encoder primaryTaint
      additionalTaints).items.map
        (fun item => item.lowered.instruction) = source.authored.instructions := by
  change (emitRawProgram checked.lower encoder primaryTaint
    additionalTaints).items.map (fun item => item.lowered.instruction) =
      source.authored.instructions
  exact (emitRawProgram.instructionsExact checked.lower encoder primaryTaint
    additionalTaints).trans checked.lower_instructions_exact

/-- Verified raw bytes are the original pre-alpha instructions encoded in
authored order by the explicitly supplied raw encoder. -/
theorem bytesExact
    {State : Type u} {Terminal : Type v} {Instruction : Type w}
    {Annotation : Type x} {Effect : Type y}
    {semantics : Semantics Instruction State}
    {effectModel : EffectModel Instruction Effect}
    [DecidableEq Terminal]
    {source : PreAlphaConstructionSource State Terminal Instruction Annotation
      Effect semantics effectModel}
    {model : LabelAlphaModel}
    (checked : VerifiedConstructionElaborated source model)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := []) :
    (emitVerifiedConstructionRaw checked encoder primaryTaint
      additionalTaints).bytes =
      source.authored.instructions.flatMap encoder.encode := by
  change (emitRawProgram checked.lower encoder primaryTaint
    additionalTaints).bytes =
      source.authored.instructions.flatMap encoder.encode
  calc
    _ = checked.lower.items.flatMap
        (fun item => encoder.encode item.instruction) :=
      emitRawProgram.bytesExact checked.lower encoder primaryTaint
        additionalTaints
    _ = (checked.lower.items.map LoweredInstruction.instruction).flatMap
        encoder.encode := by simp [List.flatMap_map]
    _ = _ := by rw [checked.lower_instructions_exact]

end emitVerifiedConstructionRaw

end Grass.Unsafe
