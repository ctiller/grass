import Grass.Construct.Source.Ast

/-!
# Derived authored-source manifest

`Ast.manifest` derives one per-block record containing canonical boundary
identities, exact outgoing edges, structural instruction origins, and instruction
counts. The manifest is a projection of the authored AST; it is never maintained
as a parallel input.
-/

namespace Grass.Construct.Source

open Grass.CFG Grass.Construct.Fragment

universe u v w x

/-- Canonical source and boundary identities for one authored block. -/
structure BlockManifest (Terminal : Type v) where
  id : BlockId
  declaredExits : List ExitTag
  outgoing : List (Edge Terminal)
  origins : List SourceOrigin
  instructionCount : Nat
deriving Repr, DecidableEq

/-- Complete derived manifest in authored block order. -/
structure Manifest (Terminal : Type v) where
  entry : BlockId
  blocks : List (BlockManifest Terminal)
deriving Repr, DecidableEq

namespace Block

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x}

/-- Derive one exact manifest record from one authored block. -/
def manifest (block : Block State Terminal Instruction Annotation) :
    BlockManifest Terminal where
  id := block.cfg.id
  declaredExits := block.cfg.contract.exitTags
  outgoing := block.cfg.outgoing
  origins := block.body.expandLocated.map LocatedInstruction.origin
  instructionCount := block.body.instructionCount

end Block

namespace Manifest

variable {Terminal : Type v}

/-- Stable block identities in exact manifest order. -/
def blockIds (manifest : Manifest Terminal) : List BlockId :=
  manifest.blocks.map BlockManifest.id

/-- Total instruction count derived across every manifested block. -/
def instructionCount (manifest : Manifest Terminal) : Nat :=
  (manifest.blocks.map BlockManifest.instructionCount).sum

/-- Find one manifested block by its stable boundary identity. -/
def findBlock? (manifest : Manifest Terminal) (id : BlockId) :
    Option (BlockManifest Terminal) :=
  manifest.blocks.find? fun block => block.id == id

end Manifest

namespace Ast

variable {State : Type u} {Terminal : Type v} {Instruction : Type w}
  {Annotation : Type x}

/-- Derive the canonical per-block source manifest from one authored AST. -/
def manifest (source : Ast State Terminal Instruction Annotation) :
    Manifest Terminal :=
  ⟨source.entry, source.blocks.map Block.manifest⟩

@[simp] theorem manifest_entry (source : Ast State Terminal Instruction Annotation) :
    source.manifest.entry = source.entry := rfl

/-- `manifest_blockIds` proves exact preservation of authored block order. -/
@[simp] theorem manifest_blockIds
    (source : Ast State Terminal Instruction Annotation) :
    source.manifest.blockIds = source.blockIds := by
  simp [manifest, Manifest.blockIds, blockIds, Block.manifest]

/-- `manifest_declaredExits` exposes every exact contract exit family. -/
@[simp] theorem manifest_declaredExits
    (source : Ast State Terminal Instruction Annotation) :
    source.manifest.blocks.map BlockManifest.declaredExits =
      source.blocks.map fun block => block.cfg.contract.exitTags := by
  simp [manifest, Block.manifest]

/-- `manifest_outgoing` exposes every exact authored edge list. -/
@[simp] theorem manifest_outgoing
    (source : Ast State Terminal Instruction Annotation) :
    source.manifest.blocks.map BlockManifest.outgoing =
      source.blocks.map fun block => block.cfg.outgoing := by
  simp [manifest, Block.manifest]

/-- `manifest_origins` exposes every exact structural instruction origin. -/
@[simp] theorem manifest_origins
    (source : Ast State Terminal Instruction Annotation) :
    source.manifest.blocks.map (fun block => (block.id, block.origins)) =
      source.expandedBlocks.map fun block =>
        (block.1, block.2.map LocatedInstruction.origin) := by
  simp [manifest, Block.manifest, expandedBlocks]

/-- `manifest_instructionCount` proves the manifest count equals authored size. -/
@[simp] theorem manifest_instructionCount
    (source : Ast State Terminal Instruction Annotation) :
    source.manifest.instructionCount = source.instructionCount := by
  simp [manifest, Manifest.instructionCount, instructionCount, List.map_map,
    Function.comp_def, Block.manifest]

/-- Manifest lookup is the exact manifest projection of authored block lookup. -/
theorem manifest_findBlock?
    (source : Ast State Terminal Instruction Annotation) (id : BlockId) :
    source.manifest.findBlock? id = (source.findBlock? id).map Block.manifest := by
  simp only [manifest, Manifest.findBlock?, findBlock?, List.find?_map]
  rfl

end Ast

end Grass.Construct.Source
