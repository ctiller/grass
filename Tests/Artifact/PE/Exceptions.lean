import Grass.Artifact.PE.ImageRoundTrip
import Grass.Artifact.PE.LayoutBinding
import Grass.Artifact.PE.ExceptionReader

/-! Container coupling fixtures with a small synthetic code/unwind payload.
Root's Hello composition still owns source-derived ABI validity and execution. -/
namespace Tests.Artifact.PE.Exceptions

open Grass.Grammar Grass.Std.Logical Grass.Artifact.PE

def textSection : RawSection :=
  ⟨⟨Vec.fromList [46, 116, 101, 120, 116], by decide⟩,
    Vec.fromList [0x48, 0x83, 0xec, 0x28, 0xcc], 0x60000020⟩
def tableSection : RawSection :=
  ⟨⟨Vec.fromList [46, 112, 100, 97, 116, 97], by decide⟩,
    Vec.replicate 12 0, 0x40000040⟩
def unwindSection : RawSection :=
  ⟨⟨Vec.fromList [46, 120, 100, 97, 116, 97], by decide⟩,
    Vec.fromList [1, 4, 1, 0, 4, 0x42, 0, 0], 0x40000040⟩
def binding : RuntimeFunctionBinding :=
  ⟨⟨⟨0, 0⟩, textSection.contents.length⟩,
    ⟨⟨2, 0⟩, unwindSection.contents.length⟩, unwindSection.contents⟩
def tableDescription : ExceptionTableDescription :=
  ⟨⟨⟨1, 0⟩, 12⟩, Vec.singleton binding⟩
def prototype : ExecutableImageDescription :=
  ⟨⟨0, 0⟩, Vec.fromList [textSection, tableSection, unwindSection], Vec.empty, none⟩
def prototypeLayout := (resolveImageLayout? prototype).get (by decide)
def records := (resolveRuntimeFunctions? prototypeLayout.placed [binding]).get (by decide)
def finalTable : RawSection := { tableSection with contents := writeRuntimeFunctions records }
def description : ExecutableImageDescription :=
  { prototype with
    sections := Vec.fromList [textSection, finalTable, unwindSection]
    exceptionTable := some tableDescription }
def accepted (input : ExecutableImageDescription) : Bool :=
  match prepareImage input with | .ok _ => true | .error _ => false
example : accepted description = true := by decide
def plan : ImagePlan :=
  match h : prepareImage description with
  | .ok plan => plan
  | .error _ => False.elim (by
      have ok : accepted description = true := by decide
      simp [accepted, h] at ok)

/-- Actual table fields derive from the resolved placement, not authored RVAs. -/
example : readRuntimeTable finalTable.contents =
    .done (records.map ResolvedRuntimeFunction.expectedRecord) Vec.empty :=
  readRuntimeTable_write records
example : readImage (writeImage plan) = .done plan.expectedImage Vec.empty :=
  readImage_writeImage plan
example : plan.expectedImage.optional.exceptionRva.toNat = 8192 ∧
    plan.expectedImage.optional.exceptionSize.toNat = 12 := by decide
example : records.map (fun f => (f.beginRva, f.endRva, f.unwindRva)) =
    [(4096, 4101, 12288)] := by decide

/-- A requested table with placeholder bytes is refused by final preparation. -/
example : accepted { prototype with exceptionTable := some tableDescription } = false := by decide
example : accepted { description with
    sections :=
    Vec.fromList [textSection, { finalTable with contents := finalTable.contents.set 0 42 },
      unwindSection] } = false := by decide
example : accepted { description with
    sections :=
    Vec.fromList [textSection, { finalTable with characteristics := 0xc0000040 },
      unwindSection] } = false := by decide
example : accepted { description with
    sections :=
    Vec.fromList [{ textSection with characteristics := 0x40000020 }, finalTable,
      unwindSection] } = false := by decide
example : accepted { description with exceptionTable := some { tableDescription with
    functions := Vec.singleton { binding with unwindBytes := Vec.replicate 8 0 } } } = false := by decide
example : resolveRuntimeFunctions? prototypeLayout.placed
    [binding, { binding with code := ⟨⟨0, 0⟩, 6⟩ }] = none := by decide
example : resolveRuntimeFunctions? prototypeLayout.placed
    [binding, { binding with unwind := ⟨⟨99, 0⟩, 8⟩ }] = none := by decide
example : accepted { description with
    sections := Vec.fromList [textSection, finalTable,
      { unwindSection with characteristics := 0xc0000040 }] } = false := by decide

/-- Complete serialized duplicates still fail the code-range ordering check. -/
example : accepted { description with
    sections := Vec.fromList [textSection,
      { finalTable with contents := writeRuntimeFunctions (records ++ records) }, unwindSection]
    exceptionTable := some {
      table := ⟨⟨1, 0⟩, 24⟩
      functions := Vec.fromList [binding, binding] } } = false := by decide

/-- The exclusive code end may equal the section's payload end, but cannot wrap. -/
example : resolveSectionExtent?
    (prototypeLayout.placed.map (fun placedSection =>
      { placedSection with virtualSpan := { placedSection.virtualSpan with start := 2^32 - 1 } }))
    binding.code = none := by decide

/-- All bytes fit, but the table begins at a misaligned actual RVA. -/
example : accepted { description with
    sections := Vec.fromList [textSection,
      { finalTable with contents := Vec.singleton 0 ++ finalTable.contents }, unwindSection]
    exceptionTable := some { tableDescription with table := ⟨⟨1, 1⟩, 12⟩ } } = false := by decide

example : readRuntimeTable (finalTable.contents ++ Vec.singleton 0) =
    .invalid (.malformed "PE runtime table extent is not a multiple of 12") := by
  rw [readRuntimeTable, if_neg (by decide)]

end Tests.Artifact.PE.Exceptions
