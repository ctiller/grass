import Grass.Assembly.Lower.Lowering
import Grass.Target.Raw

/-!
# The target-generic assembler

Two passes over an authored `Source` (`Grass/Assembly/Syntax/AST.lean`) against
one `Lowering` (`Grass/Assembly/Lower/Lowering.lean`), producing that ISA's
resolved instructions and a `Grass.Target.Sectioned`.

Pass 1 (`labelTable`) sums `Lowering.size` down the lines and records the
address each label lands on; duplicate labels are refused. Pass 2 (`emit`,
proved in `Lowering.lean`) hands every line the resolved symbol table and its
own address.

`Placement` says where the pieces go: the code base, named read-only blocks
after the code, an optional table of loader-filled slots, the entry label, and
the stack. Every ordering the well-formedness proof needs is *checked* by
`assemble`, so a successful assembly is well-formed unconditionally rather
than under hypotheses a caller could forget.

Nothing here names an ISA, a mnemonic, or a program.
-/

namespace Grass.Assembly.Lower

open Grass.Assembly.Syntax

variable {isa : Grass.Target.ISA}

/-! ## Pass 1 -/

/-- Walk `lines` from `addr`, appending each label's address to `table`. A
label already in `table` is a refusal, so the table answers each name once. -/
def collect (low : Lowering isa) (env : Env) :
    List Line → Nat → List (String × Nat) → Except String (List (String × Nat))
  | [], _, table => .ok table
  | line :: rest, addr, table =>
    match low.size line env with
    | .error message => .error message
    | .ok width =>
      match line with
      | .label name _ =>
          match lookup table name with
          | some _ => .error ("duplicate label: " ++ name)
          | none => collect low env rest (addr + width) (table ++ [(name, addr)])
      | _ => collect low env rest (addr + width) table

/-- Pass 1 never forgets an address it has already assigned. -/
theorem collect_mono (low : Lowering isa) (env : Env) :
    ∀ (lines : List Line) (addr : Nat) (table result : List (String × Nat))
      (name : String) (value : Nat),
      collect low env lines addr table = .ok result → lookup table name = some value →
      lookup result name = some value := by
  intro lines
  induction lines with
  | nil =>
      intro addr table result name value walked found
      rw [collect] at walked
      cases walked
      exact found
  | cons line rest ih =>
      intro addr table result name value walked found
      rw [collect] at walked
      split at walked
      · simp at walked
      · split at walked
        · split at walked
          · simp at walked
          · exact ih _ _ _ _ _ walked (lookup_append_left found _)
        · exact ih _ _ _ _ _ walked found

/-- A label's address is the code base plus the sizes of every line before it.
This is the whole content of pass 1: nothing else determines where a label
lands, so no lowering decision taken in pass 2 can move one. -/
theorem collect_label (low : Lowering isa) (env : Env) (name : String)
    (ann : List Annotation) (after : List Line) :
    ∀ (before : List Line) (addr : Nat) (table result : List (String × Nat)) (span : Nat),
      collect low env (before ++ .label name ann :: after) addr table = .ok result →
      low.sizes env before = .ok span →
      lookup result name = some (addr + span) := by
  intro before
  induction before with
  | nil =>
      intro addr table result span walked summed
      rw [Lowering.sizes] at summed
      cases summed
      rw [List.nil_append] at walked
      simp only [collect] at walked
      split at walked
      · simp at walked
      · split at walked
        · simp at walked
        · rename_i absent
          rw [Nat.add_zero]
          exact collect_mono low env _ _ _ _ _ _ walked (lookup_append_fresh absent addr)
  | cons line before ih =>
      intro addr table result span walked summed
      rw [List.cons_append, collect] at walked
      rw [Lowering.sizes] at summed
      split at walked
      · simp at walked
      · rename_i width sized
        simp only [sized] at summed
        split at summed
        · simp at summed
        · rename_i tailSpan tailSummed
          cases summed
          rw [← Nat.add_assoc]
          split at walked
          · split at walked
            · simp at walked
            · exact ih _ _ _ _ walked tailSummed
          · exact ih _ _ _ _ walked tailSummed

/-- Pass 1 over a whole source. -/
def labelTable (low : Lowering isa) (source : Source) (env : Env) (codeBase : Nat) :
    Except String (List (String × Nat)) :=
  collect low env source.lines codeBase []

/-- Pass 1, as the partial map pass 2 consumes. -/
def labelAddresses (low : Lowering isa) (source : Source) (env : Env) (codeBase : Nat) :
    Except String (String → Option Nat) :=
  match labelTable low source env codeBase with
  | .error message => .error message
  | .ok table => .ok (lookup table)

theorem labelAddress_spec (low : Lowering isa) (source : Source) (env : Env) (codeBase : Nat)
    (labels : String → Option Nat) (before after : List Line) (name : String)
    (ann : List Annotation) (span : Nat)
    (shape : source.lines = before ++ .label name ann :: after)
    (pass1 : labelAddresses low source env codeBase = .ok labels)
    (summed : low.sizes env before = .ok span) :
    labels name = some (codeBase + span) := by
  rw [labelAddresses] at pass1
  split at pass1
  · simp at pass1
  · rename_i table walked
    cases pass1
    rw [labelTable, shape] at walked
    exact collect_label low env name ann after before codeBase [] table span walked summed

/-! ## Placement -/

/-- Where the assembler puts what it produces. -/
structure Placement where
  /-- Virtual address of the code section. -/
  codeBase : Nat
  /-- Named read-only blocks, laid out in order; each name resolves through
  the symbol table to its address, which is what `Operand.symbol` and
  `Displacement.ripRelative` reach. -/
  rodata : List (String × List UInt8)
  /-- Virtual address of the data section; `none` places it directly after the
  code. -/
  dataBase : Option Nat
  /-- Platform symbols the code reaches through a loader-filled slot, as
  `(library, symbol)`. The slot of `symbol` resolves under the name
  `__imp_symbol`. -/
  imports : List (String × String)
  /-- Virtual address of the slot table; `none` places it after the data. -/
  importBase : Option Nat
  /-- The label control starts at. -/
  entry : String
  /-- Stack bytes the loader must reserve. -/
  stackBytes : Nat

/-- Bytes a slot occupies. Eight covers every 64-bit target's pointer; a
32-bit target's `Placement` still gets 8-byte slots, which is wasteful but
never wrong. -/
def slotWidth : Nat := 8

/-- The addresses of the named data blocks, laid out from `base`. -/
def dataNames (base : Nat) : List (String × List UInt8) → List (String × Nat)
  | [] => []
  | (name, bytes) :: rest => (name, base) :: dataNames (base + bytes.length) rest

/-- The data section's bytes: the blocks, concatenated in order. -/
def dataBytes : List (String × List UInt8) → List UInt8
  | [] => []
  | (_, bytes) :: rest => bytes ++ dataBytes rest

/-- The names under which the code reaches each import slot. -/
def importNames (base : Nat) : List (String × String) → List (String × Nat)
  | [] => []
  | (_, symbol) :: rest => ("__imp_" ++ symbol, base) :: importNames (base + slotWidth) rest

/-- The slot table an artifact writer fills in. -/
def importSlots (base : Nat) : List (String × String) → List Grass.Target.ImportSymbol
  | [] => []
  | (library, symbol) :: rest =>
      { library := library, symbol := symbol, slotAddress := base } ::
        importSlots (base + slotWidth) rest

theorem importSlots_range (base : Nat) :
    ∀ (entries : List (String × String)) (slot : Grass.Target.ImportSymbol),
      slot ∈ importSlots base entries →
      base ≤ slot.slotAddress ∧ slot.slotAddress < base + slotWidth * entries.length := by
  intro entries
  induction entries generalizing base with
  | nil => intro slot mem; simp [importSlots] at mem
  | cons head rest ih =>
      obtain ⟨library, symbol⟩ := head
      intro slot mem
      rw [importSlots, List.mem_cons] at mem
      cases mem with
      | inl same =>
          subst same
          refine ⟨Nat.le_refl _, ?_⟩
          simp only [List.length_cons, slotWidth]
          omega
      | inr later =>
          obtain ⟨lower, upper⟩ := ih (base + slotWidth) slot later
          simp only [List.length_cons, slotWidth] at *
          omega

/-- Address of the data section. -/
def Placement.dataAddress (place : Placement) (codeLength : Nat) : Nat :=
  place.dataBase.getD (place.codeBase + codeLength)

/-- Address of the import slot table. -/
def Placement.importAddress (place : Placement) (codeLength : Nat) : Nat :=
  place.importBase.getD (place.dataAddress codeLength + (dataBytes place.rodata).length)

/-- Whether no name in `names` is already a code label. -/
def allFresh (labels : List (String × Nat)) : List (String × Nat) → Bool
  | [] => true
  | (name, _) :: rest => (lookup labels name).isNone && allFresh labels rest

/-- Every name pass 2 can resolve: code labels first, then data blocks, then
import slots. A data or import name that is already a code label is refused
rather than shadowed, so no source can be assembled against an address it did
not write. -/
def symbolTable (low : Lowering isa) (source : Source) (env : Env) (place : Placement) :
    Except String (List (String × Nat)) :=
  match low.sizes env source.lines with
  | .error message => .error message
  | .ok codeLength =>
    match labelTable low source env place.codeBase with
    | .error message => .error message
    | .ok labels =>
      if allFresh labels (dataNames (place.dataAddress codeLength) place.rodata)
          && allFresh labels (importNames (place.importAddress codeLength) place.imports) then
        .ok (labels ++ dataNames (place.dataAddress codeLength) place.rodata
              ++ importNames (place.importAddress codeLength) place.imports)
      else .error "a data block or import slot is named after a code label"

/-- A code label keeps its pass-1 address in the merged table: nothing
appended after it can shadow it. -/
theorem symbolTable_label (low : Lowering isa) (source : Source) (env : Env) (place : Placement)
    (table : List (String × Nat)) (before after : List Line) (name : String)
    (ann : List Annotation) (span : Nat)
    (shape : source.lines = before ++ .label name ann :: after)
    (built : symbolTable low source env place = .ok table)
    (summed : low.sizes env before = .ok span) :
    lookup table name = some (place.codeBase + span) := by
  rw [symbolTable] at built
  split at built
  · simp at built
  · split at built
    · simp at built
    · rename_i labels walked
      split at built
      case isFalse => simp at built
      cases built
      rw [labelTable, shape] at walked
      have placed : lookup labels name = some (place.codeBase + span) :=
        collect_label low env name ann after before place.codeBase [] labels span walked summed
      rw [List.append_assoc]
      exact lookup_append_left placed _

/-! ## Pass 2 -/

/-- The executable section. -/
def codeSection (place : Placement) (bytes : List UInt8) : Grass.Target.Section where
  name := ".text"
  virtualAddress := place.codeBase
  bytes := bytes
  readable := true
  writable := false
  executable := true

/-- The read-only data section. -/
def rodataSection (place : Placement) (codeLength : Nat) : Grass.Target.Section where
  name := ".rodata"
  virtualAddress := place.dataAddress codeLength
  bytes := dataBytes place.rodata
  readable := true
  writable := false
  executable := false

/-- The loader-filled slot table. Writable, because filling it is a write. -/
def importSection (place : Placement) (codeLength : Nat) : Grass.Target.Section where
  name := ".idata"
  virtualAddress := place.importAddress codeLength
  bytes := List.replicate (slotWidth * place.imports.length) 0
  readable := true
  writable := true
  executable := false

/-- Assemble a source against one ISA's lowering.

Refusals, all of them checked here so the well-formedness theorem below needs
no hypotheses: an unsized or unlowerable line, a duplicate label, an unknown
entry label, an entry outside the code, a data section overlapping the code,
or a slot table overlapping the data. -/
def assemble (low : Lowering isa) (source : Source) (env : Env) (place : Placement) :
    Except String (List isa.Instr × Grass.Target.Sectioned) :=
  match low.sizes env source.lines with
  | .error message => .error message
  | .ok codeLength =>
    match symbolTable low source env place with
    | .error message => .error message
    | .ok table =>
      match lookup table place.entry with
      | none => .error ("entry label is not defined: " ++ place.entry)
      | some entryAddress =>
        if place.codeBase + codeLength ≤ place.dataAddress codeLength then
          if place.dataAddress codeLength + (dataBytes place.rodata).length
              ≤ place.importAddress codeLength then
            if place.codeBase ≤ entryAddress ∧ entryAddress < place.codeBase + codeLength then
              match low.emit env (lookup table) source.lines place.codeBase with
              | .error message => .error message
              | .ok instrs =>
                  .ok (instrs,
                    { sections :=
                        [codeSection place (isa.encodeAll instrs),
                          rodataSection place codeLength,
                          importSection place codeLength],
                      entry := entryAddress,
                      imports := importSlots (place.importAddress codeLength) place.imports,
                      stackBytes := place.stackBytes })
            else .error ("entry label is outside the code: " ++ place.entry)
          else .error "the import slot table overlaps the data section"
        else .error "the data section overlaps the code section"

/-- Everything a successful assembly established, in one place: this is what
each theorem below reads off. -/
theorem assemble_inv (low : Lowering isa) (source : Source) (env : Env) (place : Placement)
    (instrs : List isa.Instr) (program : Grass.Target.Sectioned)
    (built : assemble low source env place = .ok (instrs, program)) :
    ∃ codeLength table,
      low.sizes env source.lines = .ok codeLength ∧
      symbolTable low source env place = .ok table ∧
      lookup table place.entry = some program.entry ∧
      low.emit env (lookup table) source.lines place.codeBase = .ok instrs ∧
      (isa.encodeAll instrs).length = codeLength ∧
      place.codeBase + codeLength ≤ place.dataAddress codeLength ∧
      place.dataAddress codeLength + (dataBytes place.rodata).length
        ≤ place.importAddress codeLength ∧
      place.codeBase ≤ program.entry ∧ program.entry < place.codeBase + codeLength ∧
      program.sections =
        [codeSection place (isa.encodeAll instrs), rodataSection place codeLength,
          importSection place codeLength] ∧
      program.imports = importSlots (place.importAddress codeLength) place.imports := by
  rw [assemble] at built
  split at built
  · simp at built
  · rename_i codeLength summed
    split at built
    · simp at built
    · rename_i table symbols
      split at built
      · simp at built
      · rename_i entryAddress entryFound
        split at built
        · rename_i dataAfterCode
          split at built
          · rename_i importsAfterData
            split at built
            · rename_i entryInside
              split at built
              · simp at built
              · rename_i emitted
                rw [Except.ok.injEq, Prod.mk.injEq] at built
                obtain ⟨sameInstrs, sameProgram⟩ := built
                subst sameInstrs
                subst sameProgram
                exact ⟨codeLength, table, summed, symbols, entryFound, emitted,
                  low.emit_length env (lookup table) source.lines place.codeBase _ codeLength
                    emitted summed,
                  dataAfterCode, importsAfterData, entryInside.1, entryInside.2, rfl, rfl⟩
            · simp at built
          · simp at built
        · simp at built

/-- The code section's bytes are exactly the canonical encoding of the
instructions the assembler returned: no padding, no alignment, no relaxation
between the two. -/
theorem codeBytes_eq_encodeAll (low : Lowering isa) (source : Source) (env : Env)
    (place : Placement) (instrs : List isa.Instr) (program : Grass.Target.Sectioned)
    (built : assemble low source env place = .ok (instrs, program)) :
    ∃ rest, program.sections = codeSection place (isa.encodeAll instrs) :: rest := by
  obtain ⟨codeLength, _, _, _, _, _, _, _, _, _, _, sections, _⟩ :=
    assemble_inv low source env place instrs program built
  exact ⟨[rodataSection place codeLength, importSection place codeLength], sections⟩

/-- Decoding the code bytes from a label's offset yields exactly the
instructions the lines from that label onward lowered to. The label's own
offset is the sum of the sizes of the lines before it (`labelAddress_spec`),
so this says the label names an instruction boundary, not a byte inside one. -/
theorem decode_at_label (low : Lowering isa) (source : Source) (env : Env) (place : Placement)
    (instrs : List isa.Instr) (program : Grass.Target.Sectioned) (table : List (String × Nat))
    (before after : List Line) (name : String) (ann : List Annotation) (span fuel : Nat)
    (built : assemble low source env place = .ok (instrs, program))
    (symbols : symbolTable low source env place = .ok table)
    (shape : source.lines = before ++ .label name ann :: after)
    (summed : low.sizes env before = .ok span) :
    ∃ tail : List isa.Instr,
      lookup table name = some (place.codeBase + span) ∧
      low.emit env (lookup table) (.label name ann :: after) (place.codeBase + span) = .ok tail ∧
      (isa.encodeAll instrs).drop span = isa.encodeAll tail ∧
      (tail.length ≤ fuel → isa.decodeAll fuel ((isa.encodeAll instrs).drop span) = some tail) := by
  obtain ⟨_, table', _, symbols', _, emitted, _⟩ :=
    assemble_inv low source env place instrs program built
  rw [symbols] at symbols'
  cases symbols'
  rw [shape] at emitted
  obtain ⟨head, tail, splitOut, _, headBytes, tailEmitted⟩ :=
    low.emit_append env (lookup table) before _ place.codeBase instrs span emitted summed
  refine ⟨tail, symbolTable_label low source env place table before after name ann span shape
    symbols summed, tailEmitted, ?_, ?_⟩
  · rw [splitOut, Grass.Target.ISA.encodeAll_append, ← headBytes, List.drop_left]
  · intro enough
    rw [splitOut, Grass.Target.ISA.encodeAll_append, ← headBytes, List.drop_left]
    exact isa.decodeAll_encodeAll tail fuel enough

/-- The corollary the machine tier reads: the first instruction lowered from a
label decodes, at that label's address, to exactly that instruction. -/
theorem decode_first_at_label (low : Lowering isa) (source : Source) (env : Env)
    (place : Placement) (instrs : List isa.Instr) (program : Grass.Target.Sectioned)
    (table : List (String × Nat)) (before after : List Line) (name : String)
    (ann : List Annotation) (span : Nat) (first : isa.Instr) (more : List isa.Instr)
    (built : assemble low source env place = .ok (instrs, program))
    (symbols : symbolTable low source env place = .ok table)
    (shape : source.lines = before ++ .label name ann :: after)
    (summed : low.sizes env before = .ok span)
    (lowered : low.emit env (lookup table) (.label name ann :: after) (place.codeBase + span)
      = .ok (first :: more)) :
    isa.decode ((isa.encodeAll instrs).drop span) = some (first, (isa.encode first).length) := by
  obtain ⟨tail, _, tailEmitted, bytes, _⟩ :=
    decode_at_label low source env place instrs program table before after name ann span 0
      built symbols shape summed
  rw [lowered] at tailEmitted
  cases tailEmitted
  rw [bytes, Grass.Target.ISA.encodeAll_cons]
  exact isa.decode_encode first _

/-- `decode_at_label` with its size hypothesis discharged from the assembly
itself: splitting the source at a label is all a caller supplies. -/
theorem decode_at_label_of_split (low : Lowering isa) (source : Source) (env : Env)
    (place : Placement) (instrs : List isa.Instr) (program : Grass.Target.Sectioned)
    (table : List (String × Nat)) (before after : List Line) (name : String)
    (ann : List Annotation) (fuel : Nat)
    (built : assemble low source env place = .ok (instrs, program))
    (symbols : symbolTable low source env place = .ok table)
    (shape : source.lines = before ++ .label name ann :: after) :
    ∃ (span : Nat) (tail : List isa.Instr),
      lookup table name = some (place.codeBase + span) ∧
      low.emit env (lookup table) (.label name ann :: after) (place.codeBase + span) = .ok tail ∧
      (isa.encodeAll instrs).drop span = isa.encodeAll tail ∧
      (tail.length ≤ fuel → isa.decodeAll fuel ((isa.encodeAll instrs).drop span) = some tail) := by
  obtain ⟨codeLength, _, summed, _⟩ := assemble_inv low source env place instrs program built
  rw [shape] at summed
  obtain ⟨span, _, headSummed, _⟩ := low.sizes_append env before _ codeLength summed
  exact ⟨span, decode_at_label low source env place instrs program table before after name ann
    span fuel built symbols shape headSummed⟩

/-- A successful assembly is well-formed: the three sections are pairwise
disjoint, the entry lies inside the executable section, and every import slot
lies inside a readable one. All three come from arithmetic `assemble` itself
checked. -/
theorem assemble_wellFormed (low : Lowering isa) (source : Source) (env : Env)
    (place : Placement) (instrs : List isa.Instr) (program : Grass.Target.Sectioned)
    (built : assemble low source env place = .ok (instrs, program)) :
    program.WellFormed := by
  obtain ⟨codeLength, _, _, _, _, _, codeBytes, dataAfterCode, importsAfterData,
    entryLow, entryHigh, sections, imports⟩ :=
    assemble_inv low source env place instrs program built
  refine ⟨?_, ?_, ?_⟩
  · rw [Grass.Target.Sectioned.Disjoint, sections]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
    · intro other mem
      left
      simp at mem
      rcases mem with rfl | rfl
      · simp only [Grass.Target.Section.endAddress, codeSection, rodataSection, codeBytes]
        exact dataAfterCode
      · simp only [Grass.Target.Section.endAddress, codeSection, importSection, codeBytes]
        omega
    · intro other mem
      left
      simp at mem
      subst mem
      simp only [Grass.Target.Section.endAddress, rodataSection, importSection]
      exact importsAfterData
    · intro other mem
      simp at mem
  · refine ⟨codeSection place (isa.encodeAll instrs), ?_, ?_, rfl⟩
    · rw [sections]; exact List.mem_cons_self
    · refine ⟨entryLow, ?_⟩
      simp only [Grass.Target.Section.endAddress, codeSection, codeBytes]
      exact entryHigh
  · intro slot mem
    refine ⟨importSection place codeLength, ?_, ?_, rfl⟩
    · rw [sections]
      simp
    · rw [imports] at mem
      obtain ⟨lower, upper⟩ := importSlots_range _ _ slot mem
      refine ⟨lower, ?_⟩
      simp only [Grass.Target.Section.endAddress, importSection, List.length_replicate]
      exact upper

end Grass.Assembly.Lower
