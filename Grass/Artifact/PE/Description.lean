import Grass.Std.Logical.Vec

/-!
# Proof-relevant PE image descriptions

Instruction encoders supply opaque section bytes and a section-relative entry
location; the artifact layer owns container
names, imports, section characteristics, layout, and serialization.  Nothing in
this module imports an instruction-set namespace.

Format authority: Microsoft, [PE Format](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format),
especially "Section Table (Section Headers)" and "Import Directory Table";
retrieved 2026-09-01 in `docs/REFERENCES.md`.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical

/-- A PE section-table name. The on-disk short-name field has exactly eight
bytes; this adapter admits every byte string that fits without choosing a text
encoding. -/
structure SectionName where
  bytes : Std.Logical.ByteArray
  fitsShortField : bytes.length ≤ 8
deriving DecidableEq

/-- `SectionName.ofBytes?` constructs a name only when it fits the PE short-name field. -/
def SectionName.ofBytes? (bytes : Std.Logical.ByteArray) : Option SectionName :=
  if h : bytes.length ≤ 8 then some ⟨bytes, h⟩ else none

/-- A low-level section supplied to the PE container writer. `contents` is
already encoded machine data or metadata; `characteristics` is the PE/COFF
section flag word, not an x86 instruction fact. -/
structure RawSection where
  name : SectionName
  contents : Std.Logical.ByteArray
  characteristics : BitVec 32
deriving DecidableEq

/-- One imported symbol name, retained as bytes so the format layer does not
silently impose Unicode or locale rules. -/
structure ImportSymbol where
  name : Std.Logical.ByteArray
deriving DecidableEq

/-- One import-library request and its ordered symbols. -/
structure ImportLibrary where
  name : Std.Logical.ByteArray
  symbols : Vec ImportSymbol
deriving DecidableEq

/-- A location in one requested section. The layout resolves it to an RVA. -/
structure SectionLocation where
  sectionIndex : Nat
  offset : Nat
deriving DecidableEq

/-- The instruction-independent input to PE image construction. Section and
import order is part of the requested image. No caller-authored absolute RVA is
accepted for the entry point. -/
structure ExecutableImageDescription where
  entryPoint : SectionLocation
  sections : Vec RawSection
  imports : Vec ImportLibrary
deriving DecidableEq

end Grass.Artifact.PE
