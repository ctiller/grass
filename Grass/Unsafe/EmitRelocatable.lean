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

universe u v w x y z q

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

/-- Producer-authored symbolic link metadata kept separate from emitted bytes
and their construction source map. -/
structure RelocatableEmissionPlan (RelocKind : Type x)
    (ImportIdentity : Type y) where
  definitions : List SymbolDefinition := []
  relocations : List (RelocationRequest RelocKind) := []
  externals : List (ExternalReference ImportIdentity) := []
  entryCandidates : List SymbolId := []
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

/-- `verifiedConstructionSectionBytesExact` relates the initialized logical
section directly to the original pre-alpha authored instruction list. -/
theorem verifiedConstructionSectionBytesExact
    {Annotation : Type z} {Effect : Type q}
    {semantics : Grass.Construct.Fragment.Semantics Instruction State}
    {effectModel : Grass.Construct.Fragment.EffectModel Instruction Effect}
    [DecidableEq Terminal]
    {source : Grass.Construct.Source.PreAlphaConstructionSource State Terminal
      Instruction Annotation Effect semantics effectModel}
    {model : Grass.Construct.Source.LabelAlphaModel}
    (construction : Grass.Construct.Source.VerifiedConstructionElaborated
      source model)
    (encoder : RawEncoder Instruction) (primaryTaint : Taint)
    (additionalTaints : List Taint := [])
    {config : RelocatableEmissionConfig}
    (checked : CheckedRelocatableEmission
      (emitVerifiedConstructionRaw construction encoder primaryTaint
        additionalTaints) config) :
    checked.contribution.content.initialized.toList =
      (source.authored.instructions.flatMap encoder.encode).map
        Byte.ofUInt8 := by
  rw [checked.sectionBytesExact,
    emitVerifiedConstructionRaw.bytesExact construction encoder primaryTaint
      additionalTaints]

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

/-- Relocatable producer value with symbolic metadata supplied independently of
the checked emitted bytes and source ranges. -/
def plannedFragment
    {emission : RawProgramEmission State Terminal Instruction}
    {config : RelocatableEmissionConfig}
    (checked : CheckedRelocatableEmission emission config)
    (plan : RelocatableEmissionPlan RelocKind ImportIdentity) :
    RelocatableFragment RelocKind ImportIdentity :=
  { checked.fragment (RelocKind := RelocKind)
      (ImportIdentity := ImportIdentity) with
      definitions := plan.definitions
      relocations := plan.relocations
      externals := plan.externals
      entryCandidates := plan.entryCandidates }

/-- Adding symbolic metadata does not change the initialized section bytes. -/
@[simp] theorem plannedSectionBytesExact
    {emission : RawProgramEmission State Terminal Instruction}
    {config : RelocatableEmissionConfig}
    (checked : CheckedRelocatableEmission emission config)
    (plan : RelocatableEmissionPlan RelocKind ImportIdentity) :
    (checked.plannedFragment plan).sections.map
      (fun contribution => contribution.content.initialized.toList) =
    [emission.bytes.map Byte.ofUInt8] := rfl

/-- Adding symbolic metadata retains the exact checked construction source map. -/
@[simp] theorem plannedSourceMapExact
    {emission : RawProgramEmission State Terminal Instruction}
    {config : RelocatableEmissionConfig}
    (checked : CheckedRelocatableEmission emission config)
    (plan : RelocatableEmissionPlan RelocKind ImportIdentity) :
    (checked.plannedFragment plan).sourceMap = checked.sourceMap.entries := rfl

/-- Validate producer-authored symbolic metadata against the exact emitted
section and its already checked source map. -/
def checkPlannedFragment
    {emission : RawProgramEmission State Terminal Instruction}
    {config : RelocatableEmissionConfig}
    (checked : CheckedRelocatableEmission emission config)
    (plan : RelocatableEmissionPlan RelocKind ImportIdentity) :
    Except RawLinkError (CheckedRelocatableFragment
      (checked.plannedFragment plan)) :=
  checkRelocatableFragment (checked.plannedFragment plan)

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
