import Grass.Std.Logical.ListLookup
import Grass.Std.Logical.Vec
import Lean.Parser

/-! Typed logical static declarations. PE placement, padding, RVAs, and imports
belong to the artifact layout layer. -/
namespace Grass.Assembly.StaticObjects

/-- The logical section class requested by a static declaration. -/
inductive SectionKind where | rodata
deriving DecidableEq, Repr

/-- One named, aligned logical byte payload, before artifact placement. -/
structure Declaration where
  name : String
  alignment : Nat
  kind : SectionKind
  bytes : Grass.Std.Logical.ByteArray
deriving DecidableEq, Repr

/-- Whether a declaration requests read-only storage. -/
def Declaration.readOnly (declaration : Declaration) : Prop :=
  declaration.kind = .rodata

/-- Table validity requires unique names and positive power-of-two alignments. -/
def Valid (declarations : List Declaration) : Prop :=
  (declarations.map Declaration.name).Nodup ∧
    ∀ declaration ∈ declarations, Nat.isPowerOfTwo declaration.alignment

instance (declarations : List Declaration) : Decidable (Valid declarations) :=
  inferInstanceAs (Decidable (_ ∧ ∀ declaration ∈ declarations, _))

/-- An ordered collection of validated logical static declarations. -/
structure Table where
  private mk ::
  declarations : List Declaration
  valid : Valid declarations
deriving Repr

/-- Validate declarations and retain their authored order on success. -/
def validate? (declarations : List Declaration) : Option Table :=
  if valid : Valid declarations then some ⟨declarations, valid⟩ else none

/-- Construct a table from declarations accompanied by their validity proof. -/
def checked (declarations : List Declaration) (valid : Valid declarations) : Table :=
  ⟨declarations, valid⟩

/-- Find the declaration with the given authored name. -/
def Table.lookup? (table : Table) (name : String) : Option Declaration :=
  table.declarations.find? fun declaration => declaration.name = name

/-- `validate?_exact` states that successful validation preserves the declaration list. -/
theorem validate?_exact {declarations : List Declaration} {table : Table}
    (success : validate? declarations = some table) : table.declarations = declarations := by
  unfold validate? at success
  split at success <;> try contradiction
  cases success
  rfl

/-- Every validated table has pairwise-distinct declaration names. -/
theorem Table.names_unique (table : Table) :
    (table.declarations.map Declaration.name).Nodup := table.valid.1

/-- Every member of a validated table has a power-of-two alignment. -/
theorem Table.alignment_valid (table : Table) {declaration : Declaration}
    (member : declaration ∈ table.declarations) :
    Nat.isPowerOfTwo declaration.alignment := table.valid.2 declaration member

/-- A successful lookup returns a declaration bearing the requested name. -/
theorem Table.lookup?_name {table : Table} {name : String} {declaration : Declaration}
    (found : table.lookup? name = some declaration) :
    declaration.name = name := by
  simpa [Table.lookup?] using List.find?_some found

/-- A successful lookup returns a declaration belonging to the table. -/
theorem Table.lookup?_member {table : Table} {name : String} {declaration : Declaration}
    (found : table.lookup? name = some declaration) :
    declaration ∈ table.declarations := by
  exact List.mem_of_find?_eq_some found

/-- Every declaration is retrieved by its unique authored name. -/
theorem Table.lookup?_complete (table : Table) {declaration : Declaration}
    (member : declaration ∈ table.declarations) :
    table.lookup? declaration.name = some declaration := by
  exact Grass.Std.Logical.find?_key_of_mem table.names_unique member

end Grass.Assembly.StaticObjects

namespace Grass
/-- The authored static-object table exposed by the public Grass namespace. -/
abbrev StaticObjectTable := Assembly.StaticObjects.Table
end Grass

declare_syntax_cat static_object_decl
/-- Non-reserving parser for the static payload marker. -/
def staticObjectBytesParser : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "bytes" true
syntax (priority := high) ident ":" staticObjectBytesParser term:arg : static_object_decl

syntax "__grass_static_object_declarations" num "{" static_object_decl,* "}" : term

open Lean in
macro_rules
  | `(__grass_static_object_declarations $_alignment:num { }) => `([])
  | `(__grass_static_object_declarations $alignment:num {
        $name:ident : bytes $value:term }) => do
      let nameLiteral := Syntax.mkStrLit name.getId.toString
      `(Grass.Assembly.StaticObjects.Declaration.mk $nameLiteral $alignment
          Grass.Assembly.StaticObjects.SectionKind.rodata
          ($value : Grass.Std.Logical.ByteArray) :: [])
  | `(__grass_static_object_declarations $alignment:num {
        $name:ident : bytes $value:term,
        $rest:static_object_decl,* }) => do
      let nameLiteral := Syntax.mkStrLit name.getId.toString
      `(Grass.Assembly.StaticObjects.Declaration.mk $nameLiteral $alignment
          Grass.Assembly.StaticObjects.SectionKind.rodata
          ($value : Grass.Std.Logical.ByteArray) ::
        __grass_static_object_declarations $alignment { $rest,* })

/-- Non-reserving parser for the static-object block marker. -/
def staticObjectsParser : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "static_objects" true
/-- Non-reserving parser for the read-only data marker. -/
def staticObjectsRodataParser : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "rodata" true
/-- Non-reserving parser for the alignment marker. -/
def staticObjectsAlignParser : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "align" true

macro (priority := high) staticObjectsParser "{" staticObjectsRodataParser
    staticObjectsAlignParser alignment:num
    "{" declarations:static_object_decl,* "}" "}" : term =>
  `(Grass.Assembly.StaticObjects.checked
      (__grass_static_object_declarations $alignment { $declarations,* }) (by decide))
