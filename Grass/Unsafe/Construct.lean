import Grass.ISA.X86.Bytes

/-!
# Explicitly tainted raw construction

This module is the unchecked side of construction. It wraps existing raw values
instead of defining a competing instruction representation, and requires every
wrapper to name at least one check that has not been discharged.
`Raw.taint_map` proves that transformations preserve the same taint. There is
deliberately no operation here that removes taint or constructs a
verified-program certificate.
-/

namespace Grass.Unsafe

/-- One proof obligation deliberately absent from a raw value. -/
inductive MissingCheck where
  /-- Structural fields have not been checked for mutual consistency. -/
  | encodingShape
  /-- Mode, feature, privilege, or operand applicability has not been checked. -/
  | applicability
  /-- Step semantics have not been connected to the selected operation. -/
  | semantics
  /-- Direct and indirect control targets have not been closed over a CFG. -/
  | controlTargets
  /-- Relocations and symbolic references have not been resolved. -/
  | relocations
  /-- Citation and validation coverage has not been established. -/
  | citations
deriving Repr, DecidableEq

/-- Nonempty account of the checks missing from a raw value. -/
structure Taint where
  primary : MissingCheck
  additional : List MissingCheck := []
deriving Repr, DecidableEq

/-- Closed payload kinds admitted by the raw construction boundary. -/
inductive RawKind where
  | x86Instruction
  | bytes
deriving Repr, DecidableEq

/-- Concrete data type carried by one approved raw payload kind. -/
def RawKind.Value : RawKind → Type
  | .x86Instruction => Grass.ISA.X86.InsnEncoding
  | .bytes => Grass.Std.Logical.ByteSeq

/-- An approved raw payload accompanied by an explicit missing-check account. -/
structure Raw (kind : RawKind) where
  value : kind.Value
  taint : Taint

namespace Raw

variable {source target final : RawKind}

/-- Construct a raw value while naming its first missing proof obligation. -/
def unchecked (value : source.Value) (primary : MissingCheck)
    (additional : List MissingCheck := []) : Raw source :=
  ⟨value, ⟨primary, additional⟩⟩

/-- Apply a data transformation; `Raw.taint_map` proves its taint is unchanged. -/
def map (f : source.Value → target.Value) (raw : Raw source) : Raw target :=
  ⟨f raw.value, raw.taint⟩

@[simp] theorem value_unchecked (value : source.Value) (primary : MissingCheck)
    (additional : List MissingCheck) :
    (unchecked value primary additional).value = value := rfl

@[simp] theorem taint_unchecked (value : source.Value) (primary : MissingCheck)
    (additional : List MissingCheck) :
    (unchecked value primary additional).taint = ⟨primary, additional⟩ := rfl

@[simp] theorem value_map (f : source.Value → target.Value) (raw : Raw source) :
    (raw.map f).value = f raw.value := rfl

@[simp] theorem taint_map (f : source.Value → target.Value) (raw : Raw source) :
    (raw.map f).taint = raw.taint := rfl

/-- `Raw.map_compose` makes repeated transformations one exact taint-preserving map. -/
theorem map_compose (f : source.Value → target.Value)
    (g : target.Value → final.Value) (raw : Raw source) :
    (raw.map f).map g = raw.map (g ∘ f) := by
  cases raw
  rfl

end Raw

namespace Construct

open Grass.ISA.X86 Grass.Std.Logical

/-- Existing x86 instruction encoding marked with its missing proof obligations. -/
abbrev X86Instruction := Raw .x86Instruction

/-- Raw byte sequence retaining the proof obligations of its source. -/
abbrev Bytes := Raw .bytes

/-- Admit an x86 encoding only as explicitly tainted raw construction. -/
def x86Instruction (encoding : InsnEncoding) (primary : MissingCheck)
    (additional : List MissingCheck := []) : X86Instruction :=
  Raw.unchecked encoding primary additional

/-- `x86Instruction_taint` recovers the missing-check account exactly. -/
@[simp] theorem x86Instruction_taint (encoding : InsnEncoding)
    (primary : MissingCheck) (additional : List MissingCheck) :
    (x86Instruction encoding primary additional).taint =
      ⟨primary, additional⟩ := rfl

/-- Serialize raw x86; `Construct.x86Bytes_taint` proves its taint is unchanged. -/
def x86Bytes (instruction : X86Instruction) : Bytes :=
  Raw.map (source := .x86Instruction) (target := .bytes)
    InsnEncoding.toBytes instruction

@[simp] theorem x86Bytes_value (instruction : X86Instruction) :
    (x86Bytes instruction).value = instruction.value.toBytes := rfl

@[simp] theorem x86Bytes_taint (instruction : X86Instruction) :
    (x86Bytes instruction).taint = instruction.taint := rfl

end Construct

end Grass.Unsafe
