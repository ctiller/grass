import Grass.ISA.X86.Citation

/-! Reuse the generic Grass.Cite records currently housed under X86; no x86 ISA
semantics or dual-vendor policy is imported. No vendor PDF is redistributed. -/
namespace Grass.ISA.AArch64

open Grass.Cite

def armA64March2025 : SourceDocument :=
  { id := ⟨"arm-a64-ddi0602-id032025"⟩
    title := "Arm A64 Instruction Set for A-profile architecture"
    publisher := ⟨"Arm Limited"⟩
    revision := "DDI 0602 (ID032025), aarchmrs v2025-03_rel"
    published := none
    url := "https://documentation-service.arm.com/static/67e40f3398aa3c3b6eea6a85"
    livenessProbe := some "DDI 0602 (ID032025)"
    retrieval := .verified ⟨2026, 9, 9⟩
    policy := .referenceOnly }

/-- Exact word encoding and operand/control calculation only. Full BranchTo
system effects and fetch are not covered by the current implementation. -/
def compareZeroCitation : Citation :=
  { document := armA64March2025
    anchor :=
      { volume := none
        section_ := "CBZ"
        heading := some "Compare and branch on zero"
        table := some "Encoding for the 32-bit and 64-bit variants"
        page := some 139 }
    subjects := [⟨"Grass.ISA.AArch64.CompareZero.encode"⟩,
      ⟨"Grass.ISA.AArch64.CompareZero.decode"⟩, ⟨"Grass.ISA.AArch64.CompareZero.offset"⟩,
      ⟨"Grass.ISA.AArch64.CompareZero.isZero"⟩, ⟨"Grass.ISA.AArch64.CompareZero.execute"⟩]
    locator := "PDF page 142 (printed 139): inspect sf, fixed opcode, imm19 and Rt fields; " ++
      "decode sign-extension and Operation branch condition. Read with the A64 guide's " ++
      "zero-register and sequential-control rules. This does not cover full BranchTo effects."
    confirmed := some ⟨2026, 9, 9⟩ }

/-- Encoding/decoded exception request, deliberately not CheckForSVCTrap or
CallSupervisor implementation and not a Linux contract. -/
def supervisorCallCitation : Citation :=
  { document := armA64March2025
    anchor :=
      { volume := none
        section_ := "SVC"
        heading := some "Supervisor call"
        table := some "Encoding"
        page := some 1009 }
    subjects := [⟨"Grass.ISA.AArch64.SupervisorCall.encode"⟩,
      ⟨"Grass.ISA.AArch64.SupervisorCall.decode"⟩,
      ⟨"Grass.ISA.AArch64.SupervisorCall.Request"⟩]
    locator := "PDF page 1012 (printed 1009): inspect fixed bits and imm16; Operation calls " ++
      "CheckForSVCTrap before CallSupervisor. The current receipt stops before these calls."
    confirmed := some ⟨2026, 9, 9⟩ }

def armA64Guide13 : SourceDocument :=
  { id := ⟨"arm-a64-guide-102374-0103-01-en"⟩
    title := "Learn the architecture - A64 Instruction Set Architecture Guide"
    publisher := ⟨"Arm Limited"⟩
    revision := "102374_0103_01_en, 1.3"
    published := none
    url := "https://documentation-service.arm.com/static/68cd1a81cccf2a5517018d62"
    livenessProbe := some "102374_0103_01_en"
    retrieval := .verified ⟨2026, 9, 9⟩
    policy := .referenceOnly }

def registerControlCitation : Citation :=
  { document := armA64Guide13
    anchor :=
      { volume := none
        section_ := "6, 7, 22"
        heading := some "Registers in AArch64; Program flow"
        table := some "Figure 6-1"
        page := some 12 }
    subjects := [⟨"Grass.ISA.AArch64.Cpu"⟩, ⟨"Grass.ISA.AArch64.Cpu.readZero"⟩,
      ⟨"Grass.ISA.AArch64.CompareZero.isZero"⟩, ⟨"Grass.ISA.AArch64.CompareZero.nextPc"⟩]
    locator := "Pages 12 and 14: W/X views of the same register, 31 stored GPRs, zero register " ++
      "and distinct PC. Page 43: ordinary sequential control. Combine with the CBZ encoding " ++
      "and operation entry for the four-byte body successor; no fetch or exception adequacy claim."
    confirmed := some ⟨2026, 9, 9⟩ }

def svcRoutingCitation : Citation :=
  { document := armA64March2025
    anchor := { volume := none, section_ := "Shared pseudocode: SVC routing"
                heading := some "CheckForSVCTrap; CallSupervisor", table := none
                page := some 5410 }
    subjects := [⟨"Grass.ISA.AArch64.SupervisorCall.Routing.check"⟩,
      ⟨"Grass.ISA.AArch64.SupervisorCall.Routing.select"⟩,
      ⟨"Grass.ISA.AArch64.SupervisorCall.Routing.Route.preferredReturn"⟩]
    locator := "PDF pp.5403/5413 (printed 5400/5410), EL2Enabled PDF p.5973 " ++
      "(printed 5970), ELIsInHost PDF p.5975 (printed 5972). Routing-only " ++
      "non-secure non-VHE A64 EL0 projection; not SSAdvance or TakeException."
    confirmed := some ⟨2026, 9, 9⟩ }

def citations : List Citation :=
  [compareZeroCitation, supervisorCallCitation, registerControlCitation, svcRoutingCitation]

theorem citations_checked : ∀ citation ∈ citations,
    citation.WellFormed ∧ citation.FullyChecked := by
  intro citation member
  simp only [citations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

end Grass.ISA.AArch64
