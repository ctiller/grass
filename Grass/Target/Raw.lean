/-!
# Assembled native programs

`Sectioned` is the assembled form shared by every native (byte-addressed) ISA:
named sections placed at virtual addresses, an entry address, the import slots
the code reads to reach platform services, and the stack the loader must
provide. Artifact formats (PE, ELF, flat boot image) serialize it; the ISA's
`initial` installs it. Wasm has its own module form (`Grass.ISA.Wasm.Module`).

Nothing here is program-specific: a section is bytes at an address with
permissions, nothing more.
-/

namespace Grass.Target

/-- A placed section. -/
structure Section where
  name : String
  virtualAddress : Nat
  bytes : List UInt8
  readable : Bool
  writable : Bool
  executable : Bool
  deriving Repr, DecidableEq

/-- A platform symbol the program reaches through a slot the loader fills
(a PE import-address-table entry, an ELF GOT entry). -/
structure ImportSymbol where
  library : String
  symbol : String
  slotAddress : Nat
  deriving Repr, DecidableEq

/-- An assembled native program. -/
structure Sectioned where
  sections : List Section
  entry : Nat
  imports : List ImportSymbol
  /-- Stack bytes the loader must reserve below the initial stack pointer. -/
  stackBytes : Nat
  deriving Repr, DecidableEq

namespace Section

/-- The half-open byte range a section occupies. -/
def endAddress (sec : Section) : Nat :=
  sec.virtualAddress + sec.bytes.length

/-- Whether an address lies inside the section. -/
def Contains (sec : Section) (address : Nat) : Prop :=
  sec.virtualAddress ≤ address ∧ address < sec.endAddress

instance (sec : Section) (address : Nat) : Decidable (sec.Contains address) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The byte at an address inside the section. -/
def byteAt (sec : Section) (address : Nat) : Option UInt8 :=
  if sec.virtualAddress ≤ address then
    sec.bytes[address - sec.virtualAddress]?
  else none

end Section

namespace Sectioned

/-- The section containing an address, if any. Overlapping sections are a
well-formedness failure the artifact writer must refuse. -/
def sectionAt (program : Sectioned) (address : Nat) : Option Section :=
  program.sections.find? fun sec => decide (sec.Contains address)

/-- Sections occupy pairwise disjoint address ranges. -/
def Disjoint (program : Sectioned) : Prop :=
  program.sections.Pairwise fun left right =>
    left.endAddress ≤ right.virtualAddress ∨ right.endAddress ≤ left.virtualAddress

/-- The entry address lies in an executable section. -/
def EntryExecutable (program : Sectioned) : Prop :=
  ∃ sec ∈ program.sections, sec.Contains program.entry ∧ sec.executable = true

/-- Every import slot lies in a readable, non-executable section. -/
def ImportsReadable (program : Sectioned) : Prop :=
  ∀ import_ ∈ program.imports, ∃ sec ∈ program.sections,
    sec.Contains import_.slotAddress ∧ sec.readable = true

/-- The well-formedness every artifact writer requires. -/
structure WellFormed (program : Sectioned) : Prop where
  disjoint : program.Disjoint
  entryExecutable : program.EntryExecutable
  importsReadable : program.ImportsReadable

end Sectioned

end Grass.Target
