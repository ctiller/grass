import Grass.ISA.X86.Profile
import Grass.ISA.X86.Decode

/-! Regression checks for the bounded 4.09 → 4.10 source migration.
These check recorded identities, mapping and scope, not the truth of manuals. -/
namespace Grass.Tests.ISA.X86.AmdSourceMigration

open Grass.Core Grass.Cite Grass.ISA.X86
set_option maxRecDepth 4096

example : Rules.all.map (·.subject.text) =
    ["Grass.ISA.X86.writeBack", "Grass.ISA.X86.Rex.toByte",
     "Grass.ISA.X86.ByteReg.Encodable", "Grass.ISA.X86.ModRm.toByte",
     "Grass.ISA.X86.Sib.toByte", "Grass.ISA.X86.decodeMem.ripRelative",
     "Grass.ISA.X86.decodeMem.sibEscape", "Grass.ISA.X86.decodeMem.noIndex",
     "Grass.ISA.X86.decodeMem.noBase"] := by decide

example : Vendor.amd.document.id.text = "amd64-apm-40332-4.10" := rfl
example : amd64Apm409.id ≠ amd64Apm410.id := by decide
example : amd64Apm409.IsReleaseBlocker := by decide
example : amd64Apm409.policy = .referenceOnly ∧
    amd64Apm410.policy = .referenceOnly := by decide
example : openReleaseBlockers = [] := by decide
example : openAnchorConfirmations.map (·.subjects.map (·.text)) =
    [["Grass.ISA.X86.Rex.toByte"]] := by decide
example : ¬ commonProfileLedger.CitationsChecked := by decide
example : ¬ Rules.rexPrefixLayout.citation.amd.FullyChecked := by decide

example : Rules.all.map (fun r =>
    (r.citation.amd.anchor.section_, r.citation.amd.anchor.page)) =
    [("3.1.2", some 26), ("1.2.7", some 14), ("1.8.1", some 26),
     ("1.4.1", some 17), ("1.4.2", some 19), ("1.7", some 24),
     ("1.8.2", some 27), ("1.8.2", some 27), ("1.8.2", some 27)] := by decide

example : Rules.all.map (fun r =>
    (r.citation.amd.anchor.volume, r.citation.amd.anchor.table)) =
    [(some "Vol. 1", none), (some "Vol. 3", none), (some "Vol. 3", none),
     (some "Vol. 3", some "Figure 1-4"), (some "Vol. 3", some "Table 1-11"),
     (some "Vol. 3", none), (some "Vol. 3", some "Table 1-17"),
     (some "Vol. 3", some "Table 1-17"),
     (some "Vol. 3", some "Table 1-17")] := by decide

-- Even forging retrieval of the old edition cannot make it the registered pin.
private def forgedOld : Citation :=
  { Rules.registerWriteExtension.citation.amd with
    document := { amd64Apm409 with retrieval := .verified amdAnchorCheckDate } }

example : forgedOld.FullyChecked := by decide
example : forgedOld.document ≠ Vendor.amd.document := by decide

private def forgedRule : CommonRule :=
  { Rules.registerWriteExtension with
    citation :=
      { Rules.registerWriteExtension.citation with
        amd := forgedOld
        amdPublisher := by decide
        amdCovers := by decide
        amdWellFormed := by decide } }

example : ¬ Rules.Registered forgedRule := by decide
example : ¬ ({ Rules.registerWriteExtension.citation.amd with
    confirmed := none } : Citation).FullyChecked := by decide

-- Canonical decoding cannot rely on the unresolved misplaced-REX behavior or
-- silently extend the default-address-size profile to address-size overrides.
example : decodeInsn [0x48, 0x66, 0x89, 0xC0] =
    .error (.unknownOpcode false 0x66) := rfl
example : decodeInsn [0x67, 0x8D, 0x05, 0, 0, 0, 0] =
    .error (.unknownOpcode false 0x67) := rfl

end Grass.Tests.ISA.X86.AmdSourceMigration
