import Grass.Assembly.Store32

/-! Closed fixtures for the symbolic store construction; no execution claim. -/
namespace Grass.Tests.Assembly.Store32

open Grass.ABI.Win64 Grass.Assembly.Store32 Grass.ISA.X86 Grass.Memory

def layout : CallFrameLayout :=
  { argumentCount := 5, localBytes := 16, localAlignment := 8,
    savedRegisters := [.r12] }

def env : SlotEnv := .empty |>.insert "transferred" 0
def input : Input := ⟨"transferred", 0x11223344⟩
def resolved? : Option Resolved := resolve? layout 0 env input

theorem the_named_store_resolves : resolved?.isSome := by decide

theorem the_resolved_value_has_one_exact_effect :
    ∀ r, resolved? = some r →
      r.writeBytes = [0x44, 0x33, 0x22, 0x11] ∧
      r.writeBytes.length = r.range.size ∧
      r.range = ⟨r.rspRootOffset + r.displacement, 4⟩ ∧
      (layout.frameRange.shift 0).Contains r.range := by
  intro r h
  refine ⟨?_, ?_, range_eq_rspRootOffset_add_displacement r,
    range_in_frame_of_resolve? h⟩
  · rw [writeBytes_of_resolve? h]
    decide
  · rw [writeBytes_length_of_resolve? h]
    rfl

theorem the_displacement_is_positive_bounded_and_untruncated :
    ∀ r, resolved? = some r →
      0 < r.displacement ∧ r.displacement < 2 ^ 31 ∧
      (BitVec.ofNat 32 r.displacement).toNat = r.displacement := by
  intro r h
  exact ⟨displacement_positive_of_resolve? h, displacement_bounded_of_resolve? h,
    displacement_roundtrip_of_resolve? h⟩

theorem the_instruction_is_the_rsp_store_and_decodes :
    ∀ r, resolved? = some r →
      movMem32Imm32 (.base .rsp (BitVec.ofNat 32 r.displacement)) input.value =
        some r.encoding ∧
      decodeInsn r.encoding.toBytes = .ok (r.encoding, []) := by
  intro r h
  rw [← operand_eq_rsp_displacement r]
  exact ⟨encoding_equation_of_resolve? h, by
    simpa using encoding_decodes_of_resolve? h []⟩

/-- A different argument count, local alignment, local size, and saved-register
set uses the same laws without importing a Spike-specific displacement. -/
def alternateLayout : CallFrameLayout :=
  { argumentCount := 8, localBytes := 32, localAlignment := 16,
    savedRegisters := [.rbx, .r12, .r13] }

def alternateEnv : SlotEnv :=
  .empty |>.insert "transferred" (alternateLayout.localBytes - 4)
def alternateResolved? : Option Resolved := resolve? alternateLayout 0 alternateEnv input

theorem the_alternate_layout_resolves : alternateResolved?.isSome := by decide

theorem the_alternate_layout_keeps_the_symbolic_laws :
    ∀ r, alternateResolved? = some r →
      (alternateLayout.frameRange.shift 0).Contains r.range ∧
      r.writeBytes = le32 input.value ∧
      (BitVec.ofNat 32 r.displacement).toNat = r.displacement ∧
      decodeInsn r.encoding.toBytes = .ok (r.encoding, []) := by
  intro r h
  exact ⟨range_in_frame_of_resolve? h, writeBytes_of_resolve? h,
    displacement_roundtrip_of_resolve? h, by
      simpa using encoding_decodes_of_resolve? h []⟩

theorem a_missing_slot_is_refused :
    resolve? layout 0 (.empty : SlotEnv) input = none := by decide

def outsideEnv : SlotEnv :=
  .empty |>.insert input.slot layout.localBytes

theorem a_slot_outside_the_local_region_is_refused :
    resolve? layout 0 outsideEnv input = none := by decide

def oversizedLayout : CallFrameLayout :=
  { argumentCount := 0, localBytes := 2 ^ 31 + 4, localAlignment := 8,
    savedRegisters := [] }

def oversizedEnv : SlotEnv := .empty |>.insert input.slot (2 ^ 31)

theorem a_displacement_outside_positive_d32_is_refused :
    resolve? oversizedLayout 0 oversizedEnv input = none := by decide

end Grass.Tests.Assembly.Store32
