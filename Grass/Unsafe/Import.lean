import Grass.Core.Name
import Grass.Unsafe.Construct

/-!
# Raw byte import boundary

`Decoder` is a machine-owner-supplied one-instruction parser. `importBytes`
accepts its output only when each step consumes an exact nonempty prefix and
every reported control target resolves through an explicit `TargetPolicy`.
The resulting `ImportedProgram` proves exact byte coverage and remains tainted;
it carries no instruction semantics or verification certificate.
-/

namespace Grass.Unsafe

open Grass.Core Grass.CFG

universe u v w x y

/-- A raw control-flow target reported by a decoder. -/
inductive ControlTarget where
  | direct (block : BlockId)
  | indirect (site : Name)
deriving Repr, DecidableEq

/-- Finite evidence supplied for one indirect-control site. -/
structure IndirectTargetEvidence (allowed : List BlockId) where
  site : Name
  targets : List BlockId
  targetsNonempty : targets ≠ []
  targetsUnique : targets.Nodup
  targetsAllowed : ∀ target ∈ targets, target ∈ allowed

/-- Exact finite control-target policy for one structurally checked CFG. -/
structure TargetPolicy (State : Type u) (Terminal : Type v) where
  graph : CFG.Graph State Terminal
  graphWellFormed : graph.WellFormed
  indirect : List (IndirectTargetEvidence graph.blockIds)
  indirectSitesUnique : (indirect.map IndirectTargetEvidence.site).Nodup

namespace TargetPolicy

/-- Find the exact finite evidence selected for one indirect-control site. -/
def indirectEvidence? {State : Type u} {Terminal : Type v}
    (policy : TargetPolicy State Terminal) (site : Name) :
    Option (IndirectTargetEvidence policy.graph.blockIds) :=
  policy.indirect.find? fun evidence => evidence.site == site

/-- Whether the policy resolves one decoder-reported control target. -/
def resolves {State : Type u} {Terminal : Type v}
    (policy : TargetPolicy State Terminal) : ControlTarget → Bool
  | .direct block => policy.graph.blockIds.contains block
  | .indirect site => (policy.indirectEvidence? site).isSome

/-- Successful indirect lookup returns evidence for the requested site. -/
theorem site_of_indirectEvidence?
    {State : Type u} {Terminal : Type v}
    {policy : TargetPolicy State Terminal} {site : Name}
    {evidence : IndirectTargetEvidence policy.graph.blockIds}
    (hfind : policy.indirectEvidence? site = some evidence) :
    evidence.site = site := by
  have matched := List.find?_some (p := fun candidate :
    IndirectTargetEvidence policy.graph.blockIds => candidate.site == site)
    (by simpa [indirectEvidence?] using hfind)
  exact LawfulBEq.eq_of_beq matched

/-- Successful indirect lookup returns evidence from the selected policy. -/
theorem mem_of_indirectEvidence?
    {State : Type u} {Terminal : Type v}
    {policy : TargetPolicy State Terminal} {site : Name}
    {evidence : IndirectTargetEvidence policy.graph.blockIds}
    (hfind : policy.indirectEvidence? site = some evidence) :
    evidence ∈ policy.indirect := by
  exact List.mem_of_find?_eq_some (by
    simpa [indirectEvidence?] using hfind)

/-- Every target returned by selected indirect evidence is a graph block. -/
theorem targetAllowed_of_indirectEvidence?
    {State : Type u} {Terminal : Type v}
    {policy : TargetPolicy State Terminal} {site : Name}
    {evidence : IndirectTargetEvidence policy.graph.blockIds}
    (_hfind : policy.indirectEvidence? site = some evidence)
    (target : BlockId) (htarget : target ∈ evidence.targets) :
    target ∈ policy.graph.blockIds :=
  evidence.targetsAllowed target htarget

/-- Indirect resolution is exactly successful finite-evidence lookup. -/
theorem resolves_indirect_iff
    {State : Type u} {Terminal : Type v}
    (policy : TargetPolicy State Terminal) (site : Name) :
    policy.resolves (.indirect site) = true ↔
      (policy.indirectEvidence? site).isSome = true := by
  rfl

end TargetPolicy

/-- Machine-parametric parser and control-target projection. -/
structure Decoder (Byte : Type w) (Instruction : Type x) (DecodeError : Type y) where
  decodeOne : List Byte → Except DecodeError (Instruction × List Byte)
  controlTargets : Instruction → List ControlTarget

/-- One decoded instruction paired with its exact input byte prefix and offset. -/
structure ImportedInstruction (Byte : Type w) (Instruction : Type x) where
  offset : Nat
  bytes : List Byte
  instruction : Instruction
  controlTargets : List ControlTarget
deriving Repr, DecidableEq

namespace ImportedInstruction

/-- First byte offset immediately after one imported instruction. -/
def endOffset {Byte : Type w} {Instruction : Type x}
    (instruction : ImportedInstruction Byte Instruction) : Nat :=
  instruction.offset + instruction.bytes.length

end ImportedInstruction

/-- Consecutive nonempty byte-slice invariant retained by imported programs. -/
def ImportReadyFrom {Byte : Type w} {Instruction : Type x} :
    Nat → List (ImportedInstruction Byte Instruction) → Prop
  | _, [] => True
  | expected, instruction :: rest =>
      instruction.offset = expected ∧ instruction.bytes ≠ [] ∧
        ImportReadyFrom instruction.endOffset rest

/-- Every decoder-reported control target resolves through the selected policy. -/
def ImportTargetsResolved {Byte : Type w} {Instruction : Type x}
    (resolves : ControlTarget → Bool) :
    List (ImportedInstruction Byte Instruction) → Prop
  | [] => True
  | instruction :: rest =>
      (∀ target ∈ instruction.controlTargets, resolves target = true) ∧
        ImportTargetsResolved resolves rest

private def importReadyFromDecidable
    {Byte : Type w} {Instruction : Type x} [DecidableEq Byte] :
    (expected : Nat) →
      (instructions : List (ImportedInstruction Byte Instruction)) →
      Decidable (ImportReadyFrom expected instructions)
  | _, [] => isTrue trivial
  | expected, instruction :: rest =>
      if offsetExact : instruction.offset = expected then
        if bytesNonempty : instruction.bytes ≠ [] then
          match importReadyFromDecidable instruction.endOffset rest with
          | isTrue restReady =>
              isTrue ⟨offsetExact, bytesNonempty, restReady⟩
          | isFalse restNotReady =>
              isFalse fun ready => restNotReady ready.2.2
        else
          isFalse fun ready => bytesNonempty ready.2.1
      else
        isFalse fun ready => offsetExact ready.1

instance {Byte : Type w} {Instruction : Type x} [DecidableEq Byte]
    (expected : Nat) (instructions : List (ImportedInstruction Byte Instruction)) :
    Decidable (ImportReadyFrom expected instructions) :=
  importReadyFromDecidable expected instructions

/-- Structured rejection from the generic byte importer. -/
inductive ImportError (DecodeError : Type y) where
  | decode (offset : Nat) (error : DecodeError)
  | stalledDecoder (offset : Nat)
  | invalidRemainder (offset : Nat)
  | unresolvedControlTarget (offset : Nat) (target : ControlTarget)
  | fuelExhausted (offset : Nat)
deriving Repr, DecidableEq

/-- Fully consumed raw bytes and their still-tainted decoded instructions. -/
structure ImportedProgram (State : Type u) (Terminal : Type v)
    (Byte : Type w) (Instruction : Type x) where
  sourceBytes : List Byte
  instructions : List (ImportedInstruction Byte Instruction)
  bytesExact : instructions.flatMap ImportedInstruction.bytes = sourceBytes
  ready : ImportReadyFrom 0 instructions
  policy : TargetPolicy State Terminal
  targetsResolved : ImportTargetsResolved policy.resolves instructions
  taint : Taint

private theorem importReady_bytesNonempty
    {Byte : Type w} {Instruction : Type x}
    (expected : Nat) (instructions : List (ImportedInstruction Byte Instruction))
    (ready : ImportReadyFrom expected instructions) :
    ∀ instruction ∈ instructions, instruction.bytes ≠ [] := by
  induction instructions generalizing expected with
  | nil => simp
  | cons head rest ih =>
      rcases ready with ⟨_, bytesNonempty, restReady⟩
      intro instruction hinstruction
      simp only [List.mem_cons] at hinstruction
      rcases hinstruction with rfl | hinstruction
      · exact bytesNonempty
      · exact ih head.endOffset restReady instruction hinstruction

private theorem importReady_bounded
    {Byte : Type w} {Instruction : Type x}
    (expected : Nat) (instructions : List (ImportedInstruction Byte Instruction))
    (ready : ImportReadyFrom expected instructions) :
    ∀ instruction ∈ instructions,
      instruction.endOffset ≤ expected +
        (instructions.flatMap ImportedInstruction.bytes).length := by
  induction instructions generalizing expected with
  | nil => simp
  | cons head rest ih =>
      rcases ready with ⟨offsetExact, _, restReady⟩
      intro instruction hinstruction
      simp only [List.mem_cons] at hinstruction
      rcases hinstruction with rfl | hinstruction
      · simp only [List.flatMap_cons, List.length_append,
          ImportedInstruction.endOffset]
        omega
      · have bound := ih head.endOffset restReady instruction hinstruction
        simp only [List.flatMap_cons, List.length_append,
          ImportedInstruction.endOffset] at bound ⊢
        omega

private theorem importReady_coversByte
    {Byte : Type w} {Instruction : Type x}
    (expected : Nat) (instructions : List (ImportedInstruction Byte Instruction))
    (ready : ImportReadyFrom expected instructions)
    (offset : Nat) (offsetLower : expected ≤ offset)
    (offsetUpper : offset < expected +
      (instructions.flatMap ImportedInstruction.bytes).length) :
    ∃ instruction ∈ instructions,
      instruction.offset ≤ offset ∧ offset < instruction.endOffset := by
  induction instructions generalizing expected with
  | nil =>
      simp only [List.flatMap_nil, List.length_nil, Nat.add_zero] at offsetUpper
      omega
  | cons head rest ih =>
      rcases ready with ⟨offsetExact, bytesNonempty, restReady⟩
      by_cases inHead : offset < head.endOffset
      · exact ⟨head, by simp, by omega, inHead⟩
      · have restUpper : offset < head.endOffset +
            (rest.flatMap ImportedInstruction.bytes).length := by
          simp only [List.flatMap_cons, List.length_append] at offsetUpper
          simp only [ImportedInstruction.endOffset]
          omega
        obtain ⟨instruction, hinstruction, lower, upper⟩ :=
          ih head.endOffset restReady (by omega) restUpper
        exact ⟨instruction, by simp [hinstruction], lower, upper⟩

private theorem importReady_offsetsAtLeast
    {Byte : Type w} {Instruction : Type x}
    (expected : Nat) (instructions : List (ImportedInstruction Byte Instruction))
    (ready : ImportReadyFrom expected instructions) :
    ∀ instruction ∈ instructions, expected ≤ instruction.offset := by
  induction instructions generalizing expected with
  | nil => simp
  | cons head rest ih =>
      rcases ready with ⟨offsetExact, bytesNonempty, restReady⟩
      intro instruction hinstruction
      simp only [List.mem_cons] at hinstruction
      rcases hinstruction with rfl | hinstruction
      · omega
      · have later := ih head.endOffset restReady instruction hinstruction
        simp only [ImportedInstruction.endOffset] at later
        omega

private theorem importReady_uniqueContaining
    {Byte : Type w} {Instruction : Type x}
    (expected offset : Nat)
    (instructions : List (ImportedInstruction Byte Instruction))
    (ready : ImportReadyFrom expected instructions)
    (left right : ImportedInstruction Byte Instruction)
    (leftMem : left ∈ instructions) (rightMem : right ∈ instructions)
    (leftLower : left.offset ≤ offset) (leftUpper : offset < left.endOffset)
    (rightLower : right.offset ≤ offset) (rightUpper : offset < right.endOffset) :
    left = right := by
  induction instructions generalizing expected with
  | nil => simp at leftMem
  | cons head rest ih =>
      rcases ready with ⟨_, _, restReady⟩
      simp only [List.mem_cons] at leftMem rightMem
      rcases leftMem with rfl | leftMem
      · rcases rightMem with rfl | rightMem
        · rfl
        · have rightLater := importReady_offsetsAtLeast left.endOffset rest
            restReady right rightMem
          omega
      · rcases rightMem with rfl | rightMem
        · have leftLater := importReady_offsetsAtLeast right.endOffset rest
            restReady left leftMem
          omega
        · exact ih head.endOffset restReady leftMem rightMem

private theorem importTargetsResolved_elim
    {Byte : Type w} {Instruction : Type x}
    (resolves : ControlTarget → Bool)
    (instructions : List (ImportedInstruction Byte Instruction))
    (resolved : ImportTargetsResolved resolves instructions) :
    ∀ instruction ∈ instructions, ∀ target ∈ instruction.controlTargets,
      resolves target = true := by
  induction instructions with
  | nil => simp
  | cons head rest ih =>
      rcases resolved with ⟨headResolved, restResolved⟩
      intro instruction hinstruction target htarget
      simp only [List.mem_cons] at hinstruction
      rcases hinstruction with rfl | hinstruction
      · exact headResolved target htarget
      · exact ih restResolved instruction hinstruction target htarget

namespace ImportedProgram

/-- Find the imported instruction whose exact byte slice contains an offset. -/
def instructionAtByte?
    {State : Type u} {Terminal : Type v} {Byte : Type w}
    {Instruction : Type x}
    (program : ImportedProgram State Terminal Byte Instruction)
    (offset : Nat) : Option (ImportedInstruction Byte Instruction) :=
  program.instructions.find? fun instruction =>
    decide (instruction.offset ≤ offset ∧ offset < instruction.endOffset)

/-- Every reported target of every accepted instruction resolves under the
exact policy retained by the imported program. -/
theorem controlTargetResolved
    {State : Type u} {Terminal : Type v} {Byte : Type w}
    {Instruction : Type x}
    (program : ImportedProgram State Terminal Byte Instruction)
    (instruction : ImportedInstruction Byte Instruction)
    (hinstruction : instruction ∈ program.instructions)
    (target : ControlTarget) (htarget : target ∈ instruction.controlTargets) :
    program.policy.resolves target = true :=
  importTargetsResolved_elim program.policy.resolves program.instructions
    program.targetsResolved instruction hinstruction target htarget

/-- Every accepted imported instruction owns a nonempty source-byte slice. -/
theorem instructionBytesNonempty
    {State : Type u} {Terminal : Type v} {Byte : Type w}
    {Instruction : Type x}
    (program : ImportedProgram State Terminal Byte Instruction)
    (instruction : ImportedInstruction Byte Instruction)
    (hinstruction : instruction ∈ program.instructions) :
    instruction.bytes ≠ [] :=
  importReady_bytesNonempty 0 program.instructions program.ready instruction
    hinstruction

/-- Every accepted imported instruction ends within the exact source bytes. -/
theorem instructionBounded
    {State : Type u} {Terminal : Type v} {Byte : Type w}
    {Instruction : Type x}
    (program : ImportedProgram State Terminal Byte Instruction)
    (instruction : ImportedInstruction Byte Instruction)
    (hinstruction : instruction ∈ program.instructions) :
    instruction.endOffset ≤ program.sourceBytes.length := by
  rw [← program.bytesExact]
  simpa using
    importReady_bounded 0 program.instructions program.ready instruction
      hinstruction

/-- A successful imported-byte lookup returns a member whose slice contains
the queried offset. -/
theorem instructionAtByte?_sound
    {State : Type u} {Terminal : Type v} {Byte : Type w}
    {Instruction : Type x}
    (program : ImportedProgram State Terminal Byte Instruction)
    (offset : Nat) (instruction : ImportedInstruction Byte Instruction)
    (hfind : program.instructionAtByte? offset = some instruction) :
    instruction ∈ program.instructions ∧ instruction.offset ≤ offset ∧
      offset < instruction.endOffset := by
  constructor
  · exact List.mem_of_find?_eq_some hfind
  · have contains := List.find?_some hfind
    simpa [instructionAtByte?] using contains

/-- Every source-byte offset belongs to one imported instruction slice. -/
theorem instructionForByte
    {State : Type u} {Terminal : Type v} {Byte : Type w}
    {Instruction : Type x}
    (program : ImportedProgram State Terminal Byte Instruction)
    (offset : Nat) (hbound : offset < program.sourceBytes.length) :
    ∃ instruction ∈ program.instructions,
      instruction.offset ≤ offset ∧ offset < instruction.endOffset := by
  have upper : offset < 0 +
      (program.instructions.flatMap ImportedInstruction.bytes).length := by
    simpa [program.bytesExact] using hbound
  exact importReady_coversByte 0 program.instructions program.ready offset
    (Nat.zero_le offset) upper

/-- Two imported instruction slices containing one byte are the same slice. -/
theorem instructionContainingByteUnique
    {State : Type u} {Terminal : Type v} {Byte : Type w}
    {Instruction : Type x}
    (program : ImportedProgram State Terminal Byte Instruction)
    (offset : Nat) (left right : ImportedInstruction Byte Instruction)
    (leftMem : left ∈ program.instructions)
    (rightMem : right ∈ program.instructions)
    (leftLower : left.offset ≤ offset) (leftUpper : offset < left.endOffset)
    (rightLower : right.offset ≤ offset) (rightUpper : offset < right.endOffset) :
    left = right :=
  importReady_uniqueContaining 0 offset program.instructions program.ready
    left right leftMem rightMem leftLower leftUpper rightLower rightUpper

/-- Imported-byte lookup succeeds exactly for the member containing the offset. -/
theorem instructionAtByte?_eq_some_iff
    {State : Type u} {Terminal : Type v} {Byte : Type w}
    {Instruction : Type x}
    (program : ImportedProgram State Terminal Byte Instruction)
    (offset : Nat) (instruction : ImportedInstruction Byte Instruction) :
    program.instructionAtByte? offset = some instruction ↔
      instruction ∈ program.instructions ∧ instruction.offset ≤ offset ∧
        offset < instruction.endOffset := by
  constructor
  · exact program.instructionAtByte?_sound offset instruction
  · intro contains
    have foundSome : (program.instructionAtByte? offset).isSome := by
      simp only [instructionAtByte?, List.find?_isSome]
      exact ⟨instruction, contains.1,
        by simp [contains.2.1, contains.2.2]⟩
    cases hfind : program.instructionAtByte? offset with
    | none => simp [hfind] at foundSome
    | some found =>
        have foundContains := program.instructionAtByte?_sound offset found hfind
        have foundExact := program.instructionContainingByteUnique offset
          found instruction foundContains.1 contains.1 foundContains.2.1
            foundContains.2.2 contains.2.1 contains.2.2
        exact congrArg some foundExact

/-- Imported-byte lookup fails exactly outside the source byte list. -/
theorem instructionAtByte?_eq_none_iff
    {State : Type u} {Terminal : Type v} {Byte : Type w}
    {Instruction : Type x}
    (program : ImportedProgram State Terminal Byte Instruction)
    (offset : Nat) :
    program.instructionAtByte? offset = none ↔
      program.sourceBytes.length ≤ offset := by
  constructor
  · intro notFound
    by_cases bound : offset < program.sourceBytes.length
    · obtain ⟨instruction, instructionMem, lower, upper⟩ :=
        program.instructionForByte offset bound
      have found := (program.instructionAtByte?_eq_some_iff offset instruction).mpr
        ⟨instructionMem, lower, upper⟩
      rw [notFound] at found
      contradiction
    · omega
  · intro outOfBounds
    cases hfind : program.instructionAtByte? offset with
    | none => rfl
    | some instruction =>
        have contains := program.instructionAtByte?_sound offset instruction hfind
        have bounded := program.instructionBounded instruction contains.1
        omega

end ImportedProgram

private structure DecodedAt (Byte : Type w) (Instruction : Type x)
    (resolves : ControlTarget → Bool) (offset : Nat) (bytes : List Byte) where
  instructions : List (ImportedInstruction Byte Instruction)
  bytesExact : instructions.flatMap ImportedInstruction.bytes = bytes
  ready : ImportReadyFrom offset instructions
  targetsResolved : ImportTargetsResolved resolves instructions

private def decodeFuel {State : Type u} {Terminal : Type v}
    {Byte : Type w} {Instruction : Type x} {DecodeError : Type y}
    [DecidableEq Byte]
    (decoder : Decoder Byte Instruction DecodeError)
    (policy : TargetPolicy State Terminal) :
    Nat → (offset : Nat) → (bytes : List Byte) →
      Except (ImportError DecodeError)
        (DecodedAt Byte Instruction policy.resolves offset bytes)
  | _, _, [] => .ok ⟨[], rfl, trivial, trivial⟩
  | 0, offset, _ :: _ => .error (.fuelExhausted offset)
  | fuel + 1, offset, head :: tail =>
      let bytes := head :: tail
      match decoder.decodeOne bytes with
      | .error error => .error (.decode offset error)
      | .ok (instruction, rest) =>
          if _progress : rest.length < bytes.length then
            let consumed := bytes.take (bytes.length - rest.length)
            if exactRemainder : consumed ++ rest = bytes then
              let targets := decoder.controlTargets instruction
              match unresolved :
                  targets.find? fun target => !policy.resolves target with
              | some target => .error (.unresolvedControlTarget offset target)
              | none =>
                  match decodeFuel decoder policy fuel (offset + consumed.length) rest with
                  | .error error => .error error
                  | .ok tail =>
                      have consumedNonempty : consumed ≠ [] := by
                        intro consumedEmpty
                        have restExact : rest = bytes := by
                          simpa [consumedEmpty] using exactRemainder
                        rw [restExact] at _progress
                        omega
                      .ok ⟨
                        ⟨offset, consumed, instruction, targets⟩ ::
                          tail.instructions,
                        by
                          simp only [List.flatMap_cons]
                          rw [tail.bytesExact]
                          simpa [bytes] using exactRemainder,
                        ⟨rfl, consumedNonempty, tail.ready⟩,
                        ⟨by
                          intro target htarget
                          have targetResolved :=
                            (List.find?_eq_none.mp unresolved) target htarget
                          simpa using targetResolved,
                          tail.targetsResolved⟩⟩
            else .error (.invalidRemainder offset)
          else .error (.stalledDecoder offset)

/-- Decode an exact byte list under a finite control-target policy.

Success retains an `importedBytes` taint and proves that concatenating every
recorded instruction prefix reproduces the input byte-for-byte. -/
def importBytes {State : Type u} {Terminal : Type v}
    {Byte : Type w} {Instruction : Type x} {DecodeError : Type y}
    [DecidableEq Byte]
    (decoder : Decoder Byte Instruction DecodeError)
    (policy : TargetPolicy State Terminal)
    (bytes : List Byte) (detail : String := "raw imported bytes") :
    Except (ImportError DecodeError)
      (ImportedProgram State Terminal Byte Instruction) :=
  match decodeFuel decoder policy bytes.length 0 bytes with
  | .error error => .error error
  | .ok decoded => .ok ⟨bytes, decoded.instructions, decoded.bytesExact,
      decoded.ready, policy, decoded.targetsResolved,
      ⟨.importedBytes, detail⟩⟩

end Grass.Unsafe
