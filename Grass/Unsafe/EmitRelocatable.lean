import Grass.Unsafe.EmitLink
import Grass.Std.Logical.HostBytes

/-!
# Checked one-section relocatable emission

`checkRelocatableEmission` joins a raw lowered-program byte stream to its
checked source map and produces a structurally checked, format-neutral
`Link.RelocatableFragment`. The bridge adds one initialized section and no
symbols or relocations; artifact formats remain responsible for serialization,
placement, and relocation policy.
-/

namespace Grass.Unsafe

open Grass.Construct.Link Grass.Std.Logical

universe u v w x y

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {RelocKind : Type x} {ImportIdentity : Type y}

/-- Format-neutral choices for wrapping one emitted byte stream as a section. -/
structure RelocatableEmissionConfig where
  fragmentId : LinkFragmentId
  sectionId : SectionId
  alignment : Nat
  class_ : SectionClass
  permissions : SectionPermissions
deriving Repr, DecidableEq

/-- `RelocatableEmissionError` records why one raw stream cannot become a
checked relocatable fragment. -/
inductive RelocatableEmissionError where
  | zeroAlignment (fragment : LinkFragmentId) (sectionId : SectionId)
  | sourceMap (error : LinkSourceMapError)
deriving Repr, DecidableEq

/-- Raw emission paired with the two structural facts needed by the
one-section relocatable projection. -/
structure CheckedRelocatableEmission
    (emission : RawProgramEmission State Terminal Instruction)
    (config : RelocatableEmissionConfig) : Type (max u v w) where
  alignmentPositive : 0 < config.alignment
  sourceMap : CheckedLinkSourceMap emission config.sectionId

namespace CheckedRelocatableEmission

/-- The sole initialized section contributed by a checked raw emission. -/
def contribution
    {emission : RawProgramEmission State Terminal Instruction}
    {config : RelocatableEmissionConfig}
    (_checked : CheckedRelocatableEmission emission config) :
    SectionContribution where
  id := config.sectionId
  alignment := config.alignment
  class_ := config.class_
  permissions := config.permissions
  content := ⟨Vec.fromList (emission.bytes.map Byte.ofUInt8), 0⟩

/-- Format-neutral relocatable value containing the exact raw bytes and source
ranges, with symbol and relocation tables deliberately empty. -/
def fragment
    {emission : RawProgramEmission State Terminal Instruction}
    {config : RelocatableEmissionConfig}
    (checked : CheckedRelocatableEmission emission config) :
    RelocatableFragment (RelocKind := RelocKind)
      (ImportIdentity := ImportIdentity) where
  id := config.fragmentId
  sections := [checked.contribution]
  definitions := []
  relocations := []
  externals := []
  entryCandidates := []
  sourceMap := checked.sourceMap.entries

/-- The contributed initialized bytes are definitionally the emitted stream. -/
@[simp] theorem sectionBytesExact
    {emission : RawProgramEmission State Terminal Instruction}
    {config : RelocatableEmissionConfig}
    (checked : CheckedRelocatableEmission emission config) :
    checked.contribution.content.initialized.toList =
      emission.bytes.map Byte.ofUInt8 := rfl

/-- `CheckedRelocatableEmission.fragmentWellFormed` discharges the generic link
schema from positive alignment and the checked source-map range laws. -/
theorem fragmentWellFormed
    {emission : RawProgramEmission State Terminal Instruction}
    {config : RelocatableEmissionConfig}
    (checked : CheckedRelocatableEmission emission config) :
    (checked.fragment (RelocKind := RelocKind)
      (ImportIdentity := ImportIdentity)).WellFormed := by
  unfold RelocatableFragment.WellFormed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [RelocatableFragment.sectionIds, fragment]
  · simp [RelocatableFragment.definedSymbolIds, fragment]
  · simp [RelocatableFragment.externalSymbolIds, fragment]
  · simp [RelocatableFragment.definedSymbolIds, fragment]
  · intro candidate hcandidate
    simp only [fragment, List.mem_singleton] at hcandidate
    subst candidate
    exact checked.alignmentPositive
  · simp [fragment]
  · simp [fragment]
  · simp [fragment]
  · simp [fragment, RelocatableFragment.definedSymbolIds]
  · intro mapped hmapped
    constructor
    · exact checked.sourceMap.entryPositive mapped hmapped
    · refine ⟨checked.contribution, ?_, ?_⟩
      · rw [checked.sourceMap.entrySectionExact mapped hmapped]
        simp [RelocatableFragment.findSection?, fragment, contribution]
      · simpa [contribution, SectionContent.initializedSize, Vec.length,
          RawProgramEmission.byteLength, List.length_map] using
          checked.sourceMap.entryBounded mapped hmapped

/-- Checked relocatable value ready for the artifact layer's independent
writer and placement checks. -/
def checkedFragment
    {emission : RawProgramEmission State Terminal Instruction}
    {config : RelocatableEmissionConfig}
    (checked : CheckedRelocatableEmission emission config) :
    CheckedRelocatableFragment
      (checked.fragment (RelocKind := RelocKind)
        (ImportIdentity := ImportIdentity)) :=
  ⟨checked.fragmentWellFormed⟩

end CheckedRelocatableEmission

/-- Validate alignment and source ranges before exposing a checked one-section
relocatable emission. -/
def checkRelocatableEmission
    (emission : RawProgramEmission State Terminal Instruction)
    (config : RelocatableEmissionConfig) :
    Except RelocatableEmissionError
      (CheckedRelocatableEmission emission config) :=
  if alignmentPositive : 0 < config.alignment then
    match checkLinkSourceMap emission config.sectionId with
    | .ok sourceMap => .ok ⟨alignmentPositive, sourceMap⟩
    | .error error => .error (.sourceMap error)
  else
    .error (.zeroAlignment config.fragmentId config.sectionId)

end Grass.Unsafe
