import Grass.Artifact.Binary.Gobj.Scope

/-!
# Versioned proof-free `.gobj` payload envelope

`GobjPayload` is the deterministic first-order serialization boundary described
by `docs/VERIFIED_OBJECTS.md`. Table bodies remain uninterpreted framed bytes in
this layer; typed section, symbol, relocation, import, and source-map codecs are
layered above without changing the envelope.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Format versions accepted by the current `.gobj` envelope reader. -/
inductive GobjFormatVersion where
  | v1
deriving DecidableEq, Repr

/-- The first-order, proof-free fields carried by one `.gobj` file. -/
structure GobjPayload where
  formatVersion : GobjFormatVersion
  scope : StableScopeId
  sections : U32LengthPrefixedBytes
  symbols : U32LengthPrefixedBytes
  relocations : U32LengthPrefixedBytes
  imports : U32LengthPrefixedBytes
  sourceMap : U32LengthPrefixedBytes
deriving DecidableEq, Repr

/-- Four-byte ASCII `.gobj` discriminator (`GOBJ`). -/
def gobjMagic : SizedByteArray 4 :=
  ⟨Vec.fromList [0x47, 0x4f, 0x42, 0x4a], by decide⟩

/-- Numeric encoding of the sole currently supported format version. -/
def GobjFormatVersion.toBits : GobjFormatVersion → BitVec 16
  | .v1 => 1

/-- Decode a supported format version or classify it as unsupported data. -/
def readGobjFormatVersion (bits : BitVec 16) :
    Except ParseError GobjFormatVersion :=
  if bits = 1 then .ok .v1
  else .error (.unsupported "unsupported .gobj format version")

/-- The version decoder inverts the canonical version encoding. -/
@[simp] theorem readGobjFormatVersion_toBits (version : GobjFormatVersion) :
    readGobjFormatVersion version.toBits = .ok version := by
  cases version
  rfl

/-- Successful version decoding occurs exactly for the canonical bits of the
returned supported version. -/
theorem readGobjFormatVersion_ok_iff (bits : BitVec 16)
    (version : GobjFormatVersion) :
    readGobjFormatVersion bits = .ok version ↔
      bits = version.toBits := by
  cases version
  simp [readGobjFormatVersion, GobjFormatVersion.toBits]

/-- Independent language for the fixed `GOBJ` discriminator. The modeled
value is trivial because the accepted bytes have exactly one inhabitant. -/
def gobjMagicFormat : Format Unit :=
  .lift (.refine (fixedBytesFormat 4) fun bytes => bytes = gobjMagic)
    fun _ => gobjMagic

/-- `derives_gobjMagic_iff` identifies the discriminator language with the
canonical four bytes while retaining an arbitrary suffix. -/
theorem derives_gobjMagic_iff {input rest : Std.Logical.ByteArray} :
    Derives gobjMagicFormat input () rest ↔
      input = writeExact gobjMagic ++ rest := by
  constructor
  · intro derivation
    have fixed := derivation.lift_inner.refine_inner
    exact (derives_repeatedBytes_iff.mp
      (derives_fixedBytes_iff.mp fixed)).1
  · intro equality
    rw [equality]
    apply Derives.lift
    apply Derives.refine
    · exact (writeExact_realizes 4).derivesWithSuffix gobjMagic rest
    · rfl

/-- Independent language for supported `.gobj` version fields. Unsupported
bit patterns have no derivation in this format. -/
def gobjFormatVersionFormat : Format GobjFormatVersion :=
  .lift (.refine (littleEndianFormat 2) fun bits => bits = 1)
    GobjFormatVersion.toBits

/-- `derives_gobjFormatVersion_iff` characterizes each supported version by
its canonical little-endian field and retained suffix. -/
theorem derives_gobjFormatVersion_iff {input rest : Std.Logical.ByteArray}
    {version : GobjFormatVersion} :
    Derives gobjFormatVersionFormat input version rest ↔
      input = writeLittleEndian (count := 2) version.toBits ++ rest := by
  constructor
  · intro derivation
    exact derives_littleEndianFormat_iff.mp
      derivation.lift_inner.refine_inner
  · intro equality
    rw [equality]
    apply Derives.lift
    apply Derives.refine
    · exact (writeLittleEndian_realizes 2).derivesWithSuffix
        version.toBits rest
    · cases version
      rfl

/-- Independent language for the mandatory zero reserved field. -/
def gobjReservedFormat : Format Unit :=
  .lift (.refine (littleEndianFormat 2) fun bits => bits = 0)
    fun _ => (0 : BitVec 16)

/-- `derives_gobjReserved_iff` characterizes the reserved field by its two
canonical zero bytes and retained suffix. -/
theorem derives_gobjReserved_iff {input rest : Std.Logical.ByteArray} :
    Derives gobjReservedFormat input () rest ↔
      input = writeLittleEndian (count := 2) (0 : BitVec 16) ++ rest := by
  constructor
  · intro derivation
    exact derives_littleEndianFormat_iff.mp
      derivation.lift_inner.refine_inner
  · intro equality
    rw [equality]
    apply Derives.lift
    apply Derives.refine
    · exact (writeLittleEndian_realizes 2).derivesWithSuffix
        (0 : BitVec 16) rest
    · rfl

/-- Compose two independent canonical prefix languages. This local algebraic
law keeps the envelope proof about formats rather than its executable reader. -/
theorem derives_canonicalSeq_iff {α β : Type}
    {first : Format α} {second : Format β}
    {writeFirst : α → Std.Logical.ByteArray}
    {writeSecond : β → Std.Logical.ByteArray}
    (firstLaw : ∀ {input rest value}, Derives first input value rest ↔
      input = writeFirst value ++ rest)
    (secondLaw : ∀ {input rest value}, Derives second input value rest ↔
      input = writeSecond value ++ rest)
    {input rest : Std.Logical.ByteArray} {firstValue : α} {secondValue : β} :
    Derives (.seq first fun _ => second) input (firstValue, secondValue) rest ↔
      input = writeFirst firstValue ++ writeSecond secondValue ++ rest := by
  constructor
  · intro derivation
    rcases derivation.seqOuterShape with
      ⟨middle, left, right, pairEq, leftDerivation, rightDerivation⟩
    injection pairEq with leftEq rightEq
    subst left
    subst right
    rw [firstLaw.mp leftDerivation, secondLaw.mp rightDerivation]
    simp [Vec.append_assoc]
  · intro equality
    rw [equality]
    exact Derives.seq
      (firstLaw.mpr (by simp [Vec.append_assoc]))
      (secondLaw.mpr rfl)

/-- Nested product retained beneath `GobjPayload` for its five independently
framed table bodies. -/
abbrev GobjBodyFields :=
  U32LengthPrefixedBytes ×
    (U32LengthPrefixedBytes ×
      (U32LengthPrefixedBytes ×
        (U32LengthPrefixedBytes × U32LengthPrefixedBytes)))

/-- Independent language for the five ordered `.gobj` table bodies. -/
def gobjBodyFieldsFormat : Format GobjBodyFields :=
  .seq u32LengthPrefixedBytesFormat fun _ =>
  .seq u32LengthPrefixedBytesFormat fun _ =>
  .seq u32LengthPrefixedBytesFormat fun _ =>
  .seq u32LengthPrefixedBytesFormat fun _ =>
    u32LengthPrefixedBytesFormat

/-- Canonical serialization of the nested body-field representation. -/
def writeGobjBodyFields (fields : GobjBodyFields) :
    Std.Logical.ByteArray :=
  writeU32LengthPrefixedBytes fields.1 ++
  writeU32LengthPrefixedBytes fields.2.1 ++
  writeU32LengthPrefixedBytes fields.2.2.1 ++
  writeU32LengthPrefixedBytes fields.2.2.2.1 ++
  writeU32LengthPrefixedBytes fields.2.2.2.2

/-- `derives_gobjBodyFields_iff` characterizes all five body frames without
consulting `readGobj`. -/
theorem derives_gobjBodyFields_iff {input rest : Std.Logical.ByteArray}
    {fields : GobjBodyFields} :
    Derives gobjBodyFieldsFormat input fields rest ↔
      input = writeGobjBodyFields fields ++ rest := by
  unfold gobjBodyFieldsFormat writeGobjBodyFields
  rw [derives_canonicalSeq_iff derives_u32LengthPrefixedBytes_iff
    (derives_canonicalSeq_iff derives_u32LengthPrefixedBytes_iff
      (derives_canonicalSeq_iff derives_u32LengthPrefixedBytes_iff
        (derives_canonicalSeq_iff derives_u32LengthPrefixedBytes_iff
          derives_u32LengthPrefixedBytes_iff)))]
  simp [Vec.append_assoc]

/-- Nested representation of the complete envelope before it is lifted to the
public `GobjPayload` structure. -/
abbrev GobjEnvelopeFields :=
  Unit × (GobjFormatVersion ×
    (Unit × (StableScopeId × GobjBodyFields)))

/-- Independent language for the discriminator, fixed fields, scope, and five
framed bodies in their required order. -/
def gobjEnvelopeFieldsFormat : Format GobjEnvelopeFields :=
  .seq gobjMagicFormat fun _ =>
  .seq gobjFormatVersionFormat fun _ =>
  .seq gobjReservedFormat fun _ =>
  .seq stableScopeIdFormat fun _ =>
    gobjBodyFieldsFormat

/-- Canonical serialization of the nested envelope representation. -/
def writeGobjEnvelopeFields (fields : GobjEnvelopeFields) :
    Std.Logical.ByteArray :=
  writeExact gobjMagic ++
  writeLittleEndian (count := 2) fields.2.1.toBits ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeStableScopeId fields.2.2.2.1 ++
  writeGobjBodyFields fields.2.2.2.2

/-- `derives_gobjEnvelopeFields_iff` characterizes the complete nested
envelope independently of the executable reader. -/
theorem derives_gobjEnvelopeFields_iff
    {input rest : Std.Logical.ByteArray} {fields : GobjEnvelopeFields} :
    Derives gobjEnvelopeFieldsFormat input fields rest ↔
      input = writeGobjEnvelopeFields fields ++ rest := by
  unfold gobjEnvelopeFieldsFormat writeGobjEnvelopeFields
  rw [derives_canonicalSeq_iff derives_gobjMagic_iff
    (derives_canonicalSeq_iff derives_gobjFormatVersion_iff
      (derives_canonicalSeq_iff derives_gobjReserved_iff
        (derives_canonicalSeq_iff derives_stableScopeId_iff
          derives_gobjBodyFields_iff)))]
  simp [Vec.append_assoc]

/-- Forget a public payload into the nested values consumed by the independent
envelope language. -/
def GobjPayload.toEnvelopeFields (payload : GobjPayload) :
    GobjEnvelopeFields :=
  ((), (payload.formatVersion, ((), (payload.scope,
    (payload.sections, (payload.symbols, (payload.relocations,
      (payload.imports, payload.sourceMap))))))))

/-- Independent typed language of canonical `.gobj` payload envelopes. -/
def gobjPayloadFormat : Format GobjPayload :=
  .lift gobjEnvelopeFieldsFormat GobjPayload.toEnvelopeFields

/-- Serialize the canonical envelope and its five independently framed bodies. -/
def writeGobj (payload : GobjPayload) : Std.Logical.ByteArray :=
  writeExact gobjMagic ++
  writeLittleEndian (count := 2) payload.formatVersion.toBits ++
  writeLittleEndian (count := 2) (0 : BitVec 16) ++
  writeStableScopeId payload.scope ++
  writeU32LengthPrefixedBytes payload.sections ++
  writeU32LengthPrefixedBytes payload.symbols ++
  writeU32LengthPrefixedBytes payload.relocations ++
  writeU32LengthPrefixedBytes payload.imports ++
  writeU32LengthPrefixedBytes payload.sourceMap

/-- `derives_gobjPayload_iff` states that the independent payload language is
exactly the canonical writer prefix with any suffix retained. -/
theorem derives_gobjPayload_iff {input rest : Std.Logical.ByteArray}
    {payload : GobjPayload} :
    Derives gobjPayloadFormat input payload rest ↔
      input = writeGobj payload ++ rest := by
  rw [show Derives gobjPayloadFormat input payload rest ↔
      Derives gobjEnvelopeFieldsFormat input payload.toEnvelopeFields rest by
    constructor
    · intro derivation
      exact derivation.lift_inner
    · intro derivation
      exact Derives.lift derivation]
  rw [derives_gobjEnvelopeFields_iff]
  simp [writeGobjEnvelopeFields, GobjPayload.toEnvelopeFields, writeGobj,
    writeGobjBodyFields, Vec.append_assoc]

/-- Read and validate the complete fixed envelope while preserving any suffix. -/
def readGobj (input : Std.Logical.ByteArray) : ParseResult GobjPayload :=
  match takeExactSized 4 input with
  | .done magic afterMagic =>
    if _magicOk : magic = gobjMagic then
      match takeLittleEndian 2 afterMagic with
      | .done versionBits afterVersion =>
        match readGobjFormatVersion versionBits with
        | .ok version =>
          match takeLittleEndian 2 afterVersion with
          | .done reserved afterReserved =>
            if _reservedOk : reserved = 0 then
              match readStableScopeId afterReserved with
              | .done scope afterScope =>
                match readU32LengthPrefixedBytes afterScope with
                | .done sections afterSections =>
                  match readU32LengthPrefixedBytes afterSections with
                  | .done symbols afterSymbols =>
                    match readU32LengthPrefixedBytes afterSymbols with
                    | .done relocations afterRelocations =>
                      match readU32LengthPrefixedBytes afterRelocations with
                      | .done imports afterImports =>
                        match readU32LengthPrefixedBytes afterImports with
                        | .done sourceMap suffix =>
                          .done {
                            formatVersion := version
                            scope := scope
                            sections := sections
                            symbols := symbols
                            relocations := relocations
                            imports := imports
                            sourceMap := sourceMap } suffix
                        | .needMore hint => .needMore hint
                        | .invalid error => .invalid error
                      | .needMore hint => .needMore hint
                      | .invalid error => .invalid error
                    | .needMore hint => .needMore hint
                    | .invalid error => .invalid error
                  | .needMore hint => .needMore hint
                  | .invalid error => .invalid error
                | .needMore hint => .needMore hint
                | .invalid error => .invalid error
              | .needMore hint => requireAfter 20 (.needMore hint)
              | .invalid error => .invalid error
            else
              .invalid (.malformed "nonzero .gobj reserved field")
          | .needMore hint => .needMore hint
          | .invalid error => .invalid error
        | .error error => .invalid error
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
    else
      .invalid (.malformed "invalid .gobj magic")
  | .needMore hint => .needMore hint
  | .invalid error => .invalid error

/-- Arbitrary successful envelope parsing is equivalent to the independent
payload format derivation. -/
theorem readGobj_done_iff (input : Std.Logical.ByteArray)
    (payload : GobjPayload) (rest : Std.Logical.ByteArray) :
    readGobj input = .done payload rest ↔
      Derives gobjPayloadFormat input payload rest := by
  rw [derives_gobjPayload_iff]
  constructor
  · intro parsed
    unfold readGobj at parsed
    split at parsed
    next magic afterMagic magicParsed =>
      split at parsed
      next magicOk =>
        split at parsed
        next versionBits afterVersion versionParsed =>
          split at parsed
          next version versionDecoded =>
            split at parsed
            next reserved afterReserved reservedParsed =>
              split at parsed
              next reservedOk =>
                split at parsed
                next scope afterScope scopeParsed =>
                  split at parsed
                  next sections afterSections sectionsParsed =>
                    split at parsed
                    next symbols afterSymbols symbolsParsed =>
                      split at parsed
                      next relocations afterRelocations relocationsParsed =>
                        split at parsed
                        next imports afterImports importsParsed =>
                          split at parsed
                          next sourceMap suffix sourceMapParsed =>
                            injection parsed with payloadEq restEq
                            subst payload
                            subst rest
                            have magicInput :=
                              (takeExactSized_realizes 4).successSound
                                input magic afterMagic magicParsed
                            have versionInput :=
                              (takeLittleEndian_realizes 2).successSound
                                afterMagic versionBits afterVersion versionParsed
                            have reservedInput :=
                              (takeLittleEndian_realizes 2).successSound
                                afterVersion reserved afterReserved reservedParsed
                            have scopeInput := derives_stableScopeId_iff.mp
                              ((readStableScopeId_done_iff afterReserved scope
                                afterScope).mp scopeParsed)
                            have sectionsInput :=
                              derives_u32LengthPrefixedBytes_iff.mp
                                ((readU32LengthPrefixedBytes_done_iff afterScope
                                  sections afterSections).mp sectionsParsed)
                            have symbolsInput :=
                              derives_u32LengthPrefixedBytes_iff.mp
                                ((readU32LengthPrefixedBytes_done_iff afterSections
                                  symbols afterSymbols).mp symbolsParsed)
                            have relocationsInput :=
                              derives_u32LengthPrefixedBytes_iff.mp
                                ((readU32LengthPrefixedBytes_done_iff afterSymbols
                                  relocations afterRelocations).mp relocationsParsed)
                            have importsInput :=
                              derives_u32LengthPrefixedBytes_iff.mp
                                ((readU32LengthPrefixedBytes_done_iff afterRelocations
                                  imports afterImports).mp importsParsed)
                            have sourceMapInput :=
                              derives_u32LengthPrefixedBytes_iff.mp
                                ((readU32LengthPrefixedBytes_done_iff afterImports
                                  sourceMap suffix).mp sourceMapParsed)
                            have magicBytes := (derives_repeatedBytes_iff.mp
                              (derives_fixedBytes_iff.mp magicInput)).1
                            have versionBytes :=
                              derives_littleEndianFormat_iff.mp versionInput
                            have reservedBytes :=
                              derives_littleEndianFormat_iff.mp reservedInput
                            have versionOk :=
                              (readGobjFormatVersion_ok_iff versionBits version).mp
                                versionDecoded
                            calc
                              input = writeExact gobjMagic ++ afterMagic := by
                                rw [magicOk] at magicBytes
                                simpa [writeExact] using magicBytes
                              _ = writeExact gobjMagic ++
                                  (writeLittleEndian (count := 2) version.toBits ++
                                    afterVersion) := by rw [versionBytes, versionOk]
                              _ = writeExact gobjMagic ++
                                  (writeLittleEndian (count := 2) version.toBits ++
                                    (writeLittleEndian (count := 2)
                                      (0 : BitVec 16) ++ afterReserved)) := by
                                rw [reservedBytes, reservedOk]
                              _ = writeGobj {
                                  formatVersion := version
                                  scope := scope
                                  sections := sections
                                  symbols := symbols
                                  relocations := relocations
                                  imports := imports
                                  sourceMap := sourceMap } ++ suffix := by
                                rw [scopeInput, sectionsInput, symbolsInput,
                                  relocationsInput, importsInput, sourceMapInput]
                                simp [writeGobj, Vec.append_assoc]
                          all_goals contradiction
                        all_goals contradiction
                      all_goals contradiction
                    all_goals contradiction
                  all_goals contradiction
                next _ hint _ =>
                  have impossible : requireAfter (α := GobjPayload) 20
                      (.needMore hint) ≠ .done payload rest := by
                    cases hint <;> simp [requireAfter]
                  exact (impossible parsed).elim
                next => contradiction
              next => contradiction
            all_goals contradiction
          next => contradiction
        all_goals contradiction
      next => contradiction
    all_goals contradiction
  · intro canonical
    rw [canonical]
    unfold readGobj writeGobj
    simp only [Vec.append_assoc]
    rw [takeExactSized_writeExact_append]
    simp only [dite_true]
    rw [takeLittleEndian_writeLittleEndian_append]
    simp only [readGobjFormatVersion_toBits]
    rw [takeLittleEndian_writeLittleEndian_append]
    simp only [dite_true]
    rw [readStableScopeId_write_append]
    simp only
    rw [readU32LengthPrefixedBytes_write_append]
    simp only
    rw [readU32LengthPrefixedBytes_write_append]
    simp only
    rw [readU32LengthPrefixedBytes_write_append]
    simp only
    rw [readU32LengthPrefixedBytes_write_append]
    simp only
    rw [readU32LengthPrefixedBytes_write_append]

/-- The independent payload language has one value and suffix for each input. -/
theorem gobjPayload_derives_deterministic
    {input : Std.Logical.ByteArray} {firstValue secondValue : GobjPayload}
    {firstRest secondRest : Std.Logical.ByteArray}
    (first : Derives gobjPayloadFormat input firstValue firstRest)
    (second : Derives gobjPayloadFormat input secondValue secondRest) :
    firstValue = secondValue ∧ firstRest = secondRest := by
  have firstParsed := (readGobj_done_iff input firstValue firstRest).mpr first
  have secondParsed := (readGobj_done_iff input secondValue secondRest).mpr second
  rw [firstParsed] at secondParsed
  injection secondParsed with valueEq restEq
  exact ⟨valueEq, restEq⟩

/-- Every successful payload parse consumes its complete nonempty canonical
envelope prefix and returns precisely the remaining suffix. -/
theorem readGobj_success_progress {input : Std.Logical.ByteArray}
    {payload : GobjPayload} {rest : Std.Logical.ByteArray}
    (parsed : readGobj input = .done payload rest) :
    ∃ consumed, input = consumed ++ rest ∧ 0 < consumed.length := by
  have canonical := derives_gobjPayload_iff.mp
    ((readGobj_done_iff input payload rest).mp parsed)
  refine ⟨writeGobj payload, canonical, ?_⟩
  simp [writeGobj]
  omega

/-- `length_writeGobj` gives the exact envelope and framed-body byte width. -/
@[simp] theorem length_writeGobj (payload : GobjPayload) :
    (writeGobj payload).length =
      28 + (writeStableScopeId payload.scope).length +
        payload.sections.bytes.length + payload.symbols.bytes.length +
        payload.relocations.bytes.length + payload.imports.bytes.length +
        payload.sourceMap.bytes.length := by
  simp [writeGobj]
  omega

/-- `readGobj_write_append` parses a canonical payload exactly and preserves
every following suffix. -/
@[simp] theorem readGobj_write_append (payload : GobjPayload)
    (suffix : Std.Logical.ByteArray) :
    readGobj (writeGobj payload ++ suffix) = .done payload suffix := by
  unfold readGobj writeGobj
  simp only [Vec.append_assoc]
  rw [takeExactSized_writeExact_append]
  simp only [dite_true]
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only [readGobjFormatVersion_toBits]
  rw [takeLittleEndian_writeLittleEndian_append]
  simp only [dite_true]
  rw [readStableScopeId_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]
  simp only
  rw [readU32LengthPrefixedBytes_write_append]

/-- `readGobj_write` is the complete-input payload round trip. -/
@[simp] theorem readGobj_write (payload : GobjPayload) :
    readGobj (writeGobj payload) = .done payload Vec.empty := by
  simpa using readGobj_write_append payload Vec.empty

/-- Canonical deterministic semantics for the `.gobj` envelope language. -/
noncomputable def gobjPayloadSemantics :
    FormatSemantics gobjPayloadFormat :=
  deterministicPrefixSemantics gobjPayloadFormat
    gobjPayload_derives_deterministic

/-- The `.gobj` writer realizes the independently defined deterministic
payload semantics. -/
theorem writeGobj_realizes :
    WriterRealizes gobjPayloadSemantics writeGobj := by
  constructor
  · intro payload
    simpa using (derives_gobjPayload_iff (payload := payload)
      (rest := Vec.empty)).mpr (by simp)
  · intro payload
    change Derives gobjPayloadFormat (writeGobj payload) payload Vec.empty
    simpa using (derives_gobjPayload_iff (payload := payload)
      (rest := Vec.empty)).mpr (by simp)

end Grass.Artifact.Binary.Gobj
