import Grass.Artifact.PE.Imports
import Grass.Artifact.Binary.Endian

/-! PE exception-directory adapter. It carries no unwind semantic validator.
Container authority: Microsoft PE Format, Exception Table; x64 Exception Handling,
RUNTIME_FUNCTION and UNWIND_INFO (retrieved 2026-09-09):
https://learn.microsoft.com/en-us/windows/win32/debug/pe-format
https://learn.microsoft.com/en-us/cpp/build/exception-handling-x64
Readonly nonexecutable metadata is this emitter's selected section profile.
-/

namespace Grass.Artifact.PE

open Grass.Std.Logical Grass.Artifact.Binary

/-- Resolve a nonempty whole-payload extent, retain its exact bytes, and reject
RVA arithmetic outside the PE32 address space before any slice is returned. -/
def resolveSectionExtent? (placed : Vec PlacedSection) (extent : SectionExtent) :
    Option (Nat × Std.Logical.ByteArray) := do
  let placedSection ← placed.get? extent.location.sectionIndex
  let offset := extent.location.offset
  let finish := offset + extent.size
  let rva := placedSection.virtualSpan.start + offset
  let rvaEnd := rva + extent.size
  if extent.size = 0 || placedSection.source.contents.length < finish || rvaEnd ≥ 2^32 then none
  else some (rva, (placedSection.source.contents.drop offset).take extent.size)

/-- A successful checked extent identifies its selected section and exact slice;
the nonempty payload bound and strict PE32 RVA end bound were all checked before
the result was constructed. -/
theorem resolveSectionExtent?_success {placed : Vec PlacedSection} {extent : SectionExtent}
    {rva : Nat} {bytes : Std.Logical.ByteArray}
    (success : resolveSectionExtent? placed extent = some (rva, bytes)) :
    ∃ placedSection, placed.get? extent.location.sectionIndex = some placedSection ∧
      0 < extent.size ∧ extent.location.offset + extent.size ≤ placedSection.source.contents.length ∧
      rva = placedSection.virtualSpan.start + extent.location.offset ∧ rva + extent.size < 2^32 ∧
      bytes = (placedSection.source.contents.drop extent.location.offset).take extent.size ∧
      bytes.length = extent.size := by
  unfold resolveSectionExtent? at success
  cases selected : placed.get? extent.location.sectionIndex with
  | none => simp [selected] at success
  | some placedSection =>
    simp only [selected] at success
    change (if extent.size = 0 ||
        placedSection.source.contents.length < extent.location.offset + extent.size ||
        placedSection.virtualSpan.start + extent.location.offset + extent.size ≥ 2^32 then none
      else some (placedSection.virtualSpan.start + extent.location.offset,
        (placedSection.source.contents.drop extent.location.offset).take extent.size)) =
      some (rva, bytes) at success
    split at success
    · simp at success
    · rename_i rejected
      simp at rejected
      simp only [Option.some.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      refine ⟨placedSection, rfl, ?_, ?_, rfl, ?_, rfl, ?_⟩
      · exact Nat.pos_of_ne_zero rejected.1.1
      · omega
      · omega
      · simp
        omega

structure ResolvedExtent where
  rva : Nat
  bytes : Std.Logical.ByteArray
deriving DecidableEq

def resolveExtent? (placed : Vec PlacedSection) (extent : SectionExtent) : Option ResolvedExtent := do
  let (rva, bytes) ← resolveSectionExtent? placed extent
  some ⟨rva, bytes⟩

theorem resolveExtent?_success {placed : Vec PlacedSection} {extent : SectionExtent}
    {resolved : ResolvedExtent}
    (success : resolveExtent? placed extent = some resolved) :
    resolveSectionExtent? placed extent = some (resolved.rva, resolved.bytes) := by
  unfold resolveExtent? at success
  cases raw : resolveSectionExtent? placed extent <;> simp [raw] at success
  rename_i pair
  cases success
  simp at raw ⊢

structure ResolvedRuntimeFunction where
  beginRva : Nat
  endRva : Nat
  unwindRva : Nat
  codeBytes : Std.Logical.ByteArray
  unwindBytes : Std.Logical.ByteArray
deriving DecidableEq

def resolveRuntimeFunction? (placed : Vec PlacedSection) (binding : RuntimeFunctionBinding) :
    Option ResolvedRuntimeFunction := do
  let code ← resolveExtent? placed binding.code
  let unwind ← resolveExtent? placed binding.unwind
  if binding.unwindBytes = unwind.bytes then
    some ⟨code.rva, code.rva + code.bytes.length, unwind.rva, code.bytes, unwind.bytes⟩
  else none

/-- A successful runtime record retains the exact checked source extents. In
particular, all serialized RVAs and the exclusive code end remain below 2^32,
so `BitVec.ofNat` in the table writer does not truncate these accepted values. -/
theorem resolveRuntimeFunction?_success {placed : Vec PlacedSection}
    {binding : RuntimeFunctionBinding} {function : ResolvedRuntimeFunction}
    (success : resolveRuntimeFunction? placed binding = some function) :
    ∃ codeRva codeBytes unwindRva unwindBytes,
      resolveSectionExtent? placed binding.code = some (codeRva, codeBytes) ∧
      resolveSectionExtent? placed binding.unwind = some (unwindRva, unwindBytes) ∧
      function.beginRva = codeRva ∧ function.endRva = codeRva + codeBytes.length ∧
      function.unwindRva = unwindRva ∧ function.codeBytes = codeBytes ∧
      function.unwindBytes = unwindBytes ∧ codeRva + codeBytes.length < 2^32 ∧
      unwindRva < 2^32 ∧ codeBytes.length = binding.code.size ∧
      unwindBytes.length = binding.unwind.size := by
  unfold resolveRuntimeFunction? at success
  cases codeResult : resolveExtent? placed binding.code with
  | none => simp [codeResult] at success
  | some code =>
    cases unwindResult : resolveExtent? placed binding.unwind with
    | none => simp [codeResult, unwindResult] at success
    | some unwind =>
      simp only [codeResult, unwindResult] at success
      change (if binding.unwindBytes = unwind.bytes then
          some ⟨code.rva, code.rva + code.bytes.length, unwind.rva, code.bytes, unwind.bytes⟩
        else none) = some function at success
      split at success
      · rename_i bytesMatch
        simp only [Option.some.injEq] at success
        rcases success with ⟨rfl, rfl⟩
        have codeRaw := resolveExtent?_success codeResult
        have unwindRaw := resolveExtent?_success unwindResult
        obtain ⟨codeSection, codeSelected, _, _, codeRvaEq, codeBound,
          codeBytesEq, codeLength⟩ := resolveSectionExtent?_success codeRaw
        obtain ⟨unwindSection, unwindSelected, _, _, unwindRvaEq, unwindBound,
          unwindBytesEq, unwindLength⟩ := resolveSectionExtent?_success unwindRaw
        refine ⟨code.rva, code.bytes, unwind.rva, unwind.bytes, codeRaw, unwindRaw,
          rfl, rfl, rfl, rfl, rfl, ?_, ?_, codeLength, unwindLength⟩
        · rw [codeLength]
          exact codeBound
        · omega
      · simp at success

/-- `resolveRuntimeFunction?_bounds` projects the no-truncation bounds from a
successful exact runtime-record resolution. -/
theorem resolveRuntimeFunction?_bounds {placed : Vec PlacedSection}
    {binding : RuntimeFunctionBinding} {function : ResolvedRuntimeFunction}
    (success : resolveRuntimeFunction? placed binding = some function) :
    function.beginRva < 2^32 ∧ function.endRva < 2^32 ∧ function.unwindRva < 2^32 := by
  obtain ⟨codeRva, codeBytes, unwindRva, unwindBytes, _, _, beginEq, endEq,
    unwindEq, _, _, codeBound, unwindBound, _, _⟩ := resolveRuntimeFunction?_success success
  constructor
  · rw [beginEq]
    omega
  constructor
  · rw [endEq]
    exact codeBound
  · rw [unwindEq]
    omega

/-- One PE runtime-function record is three little-endian RVAs. -/
def writeRuntimeFunction (function : ResolvedRuntimeFunction) : Std.Logical.ByteArray :=
  writeLittleEndian (count := 4) (BitVec.ofNat 32 function.beginRva) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 function.endRva) ++
  writeLittleEndian (count := 4) (BitVec.ofNat 32 function.unwindRva)

@[simp] theorem length_writeRuntimeFunction (function : ResolvedRuntimeFunction) :
    (writeRuntimeFunction function).length = 12 := by
  simp [writeRuntimeFunction]

/-- `writeRuntimeFunctions` produces provisional table bytes from resolved
runtime records. A caller may use it while computing a final table extent;
`exceptionTableValid` still requires the placed payload to match exactly. -/
def writeRuntimeFunctions : List ResolvedRuntimeFunction → Std.Logical.ByteArray
  | [] => Vec.empty
  | function :: rest => writeRuntimeFunction function ++ writeRuntimeFunctions rest

@[simp] theorem length_writeRuntimeFunctions (functions : List ResolvedRuntimeFunction) :
    (writeRuntimeFunctions functions).length = 12 * functions.length := by
  induction functions with
  | nil => rfl
  | cons function rest ih => simp [writeRuntimeFunctions, ih]; omega

def writeRuntimeFunctionTable (functions : Vec ResolvedRuntimeFunction) : Std.Logical.ByteArray :=
  writeRuntimeFunctions functions.toList

@[simp] theorem length_writeRuntimeFunctionTable (functions : Vec ResolvedRuntimeFunction) :
    (writeRuntimeFunctionTable functions).length = 12 * functions.length := by
  exact length_writeRuntimeFunctions functions.toList

/-- `sectionReadable` and companion constants are PE flag bits used by
container placement checks. -/
def sectionReadable : BitVec 32 := 0x40000000
def sectionExecutable : BitVec 32 := 0x20000000
def sectionDiscardable : BitVec 32 := 0x02000000
def sectionWritable : BitVec 32 := 0x80000000
def sectionInitializedData : BitVec 32 := 0x00000040
def sectionContainsCode : BitVec 32 := 0x00000020

def hasFlag (flags mask : BitVec 32) : Bool := decide (flags &&& mask ≠ 0)

def codeSectionValid? (placed : Vec PlacedSection) (extent : SectionExtent) : Bool :=
  match placed.get? extent.location.sectionIndex with
  | none => false
  | some placedSection =>
      hasFlag placedSection.source.characteristics sectionReadable &&
      hasFlag placedSection.source.characteristics sectionExecutable &&
      hasFlag placedSection.source.characteristics sectionContainsCode

def metadataSectionValid? (placed : Vec PlacedSection) (extent : SectionExtent) : Bool :=
  match placed.get? extent.location.sectionIndex with
  | none => false
  | some placedSection =>
      hasFlag placedSection.source.characteristics sectionReadable &&
      hasFlag placedSection.source.characteristics sectionInitializedData &&
      !hasFlag placedSection.source.characteristics sectionWritable &&
      !hasFlag placedSection.source.characteristics sectionExecutable &&
      !hasFlag placedSection.source.characteristics sectionDiscardable

def extentDisjoint (left right : SectionExtent) : Bool :=
  left.location.sectionIndex ≠ right.location.sectionIndex ||
    left.location.offset + left.size ≤ right.location.offset ||
    right.location.offset + right.size ≤ left.location.offset

/-- Runtime records are sorted by code start and their code ranges do not
overlap. Equality at a predecessor's exclusive end is allowed. -/
def runtimeFunctionsAscending? : List ResolvedRuntimeFunction → Bool
  | [] => true
  | function :: rest =>
      rest.all (fun next => decide (function.beginRva < next.beginRva) &&
        decide (function.endRva ≤ next.beginRva)) && runtimeFunctionsAscending? rest

def resolveRuntimeFunctions? (placed : Vec PlacedSection) : List RuntimeFunctionBinding →
    Option (List ResolvedRuntimeFunction)
  | [] => some []
  | binding :: rest => do
      let function ← resolveRuntimeFunction? placed binding
      let resolved ← resolveRuntimeFunctions? placed rest
      some (function :: resolved)

/-- A successful sequence resolution has one runtime record for every supplied
binding; failure is never represented by dropping an entry. -/
theorem resolveRuntimeFunctions?_length {placed : Vec PlacedSection}
    {bindings : List RuntimeFunctionBinding} {functions : List ResolvedRuntimeFunction}
    (success : resolveRuntimeFunctions? placed bindings = some functions) :
    functions.length = bindings.length := by
  induction bindings generalizing functions with
  | nil => simpa [resolveRuntimeFunctions?] using success
  | cons binding rest ih =>
      unfold resolveRuntimeFunctions? at success
      cases resolved : resolveRuntimeFunction? placed binding <;> simp [resolved] at success
      rename_i function
      cases tail : resolveRuntimeFunctions? placed rest <;> simp [tail] at success
      rename_i functions
      obtain ⟨rfl, success⟩ := success
      simp [ih tail]

/-- Every record in a successful sequence result is the exact successful
resolution of one supplied binding. -/
theorem resolveRuntimeFunctions?_member {placed : Vec PlacedSection}
    {bindings : List RuntimeFunctionBinding} {functions : List ResolvedRuntimeFunction}
    (success : resolveRuntimeFunctions? placed bindings = some functions)
    {function : ResolvedRuntimeFunction} (member : function ∈ functions) :
    ∃ binding ∈ bindings, resolveRuntimeFunction? placed binding = some function := by
  induction bindings generalizing functions with
  | nil =>
      simp [resolveRuntimeFunctions?] at success
      subst functions
      simp at member
  | cons binding rest ih =>
      unfold resolveRuntimeFunctions? at success
      cases headResult : resolveRuntimeFunction? placed binding <;> simp [headResult] at success
      rename_i head
      cases tailResult : resolveRuntimeFunctions? placed rest <;> simp [tailResult] at success
      rename_i tail
      cases success
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨binding, List.mem_cons_self, headResult⟩
      · obtain ⟨binding, present, resolved⟩ := ih tailResult member
        exact ⟨binding, List.mem_cons_of_mem _ present, resolved⟩

def runtimeBindingValid? (placed : Vec PlacedSection)
    (binding : RuntimeFunctionBinding) (function : ResolvedRuntimeFunction) : Bool :=
  codeSectionValid? placed binding.code && metadataSectionValid? placed binding.unwind &&
  decide (function.beginRva < function.endRva) &&
  decide (function.unwindRva % 4 = 0) &&
  decide (function.unwindBytes.length ≥ 4) &&
  decide (function.unwindBytes.length % 4 = 0) &&
  decide (binding.unwindBytes.length = binding.unwind.size)

def runtimeBindingsValid? (placed : Vec PlacedSection) :
    List RuntimeFunctionBinding → List ResolvedRuntimeFunction → Bool
  | [], [] => true
  | binding :: bindings, function :: functions =>
      runtimeBindingValid? placed binding function && runtimeBindingsValid? placed bindings functions
  | _, _ => false

/-- Total container validator for a final exception table. The provisional
writer above is intentionally insufficient: this check resolves every source
binding, requires all twelve-byte records, and compares the actual table payload
against the complete resolved serialization. -/
def exceptionTableValid (placed : Vec PlacedSection)
    (description : ExceptionTableDescription) : Bool :=
  match resolveSectionExtent? placed description.table,
      resolveRuntimeFunctions? placed description.functions.toList with
  | some (tableRva, tableBytes), some functions =>
      decide (0 < description.functions.length) &&
      metadataSectionValid? placed description.table &&
      decide (tableRva % 4 = 0) &&
      decide (description.table.size = 12 * description.functions.length) &&
      decide (tableBytes = writeRuntimeFunctions functions) &&
      runtimeBindingsValid? placed description.functions.toList functions &&
      runtimeFunctionsAscending? functions &&
      description.functions.toList.all fun binding =>
        extentDisjoint description.table binding.unwind
  | _, _ => false

/-- Facts extracted from a successful total exception-table check. This is an
output of `exceptionTableValid = true`, never a certificate supplied in place of
the checker. -/
structure ExceptionTableEvidence (placed : Vec PlacedSection)
    (description : ExceptionTableDescription) where
  tableRva : Nat
  tableBytes : Std.Logical.ByteArray
  functions : List ResolvedRuntimeFunction
  tableResolved : resolveSectionExtent? placed description.table = some (tableRva, tableBytes)
  functionsResolved : resolveRuntimeFunctions? placed description.functions.toList = some functions
  nonempty : 0 < description.functions.length
  tableMetadata : metadataSectionValid? placed description.table = true
  tableAligned : tableRva % 4 = 0
  tableSize : description.table.size = 12 * description.functions.length
  tableBytesExact : tableBytes = writeRuntimeFunctions functions
  bindingsValid : runtimeBindingsValid? placed description.functions.toList functions = true
  ascending : runtimeFunctionsAscending? functions = true
  tableUnwindDisjoint : description.functions.toList.all
    (fun binding => extentDisjoint description.table binding.unwind) = true

/-- Successful validation exposes the actual table slice and complete resolved
record list together with every Boolean guard that accepted them. -/
theorem exceptionTableValid_evidence {placed : Vec PlacedSection}
    {description : ExceptionTableDescription}
    (valid : exceptionTableValid placed description = true) :
    Nonempty (ExceptionTableEvidence placed description) := by
  unfold exceptionTableValid at valid
  cases tableResult : resolveSectionExtent? placed description.table with
  | none => simp [tableResult] at valid
  | some table =>
    cases functionsResult : resolveRuntimeFunctions? placed description.functions.toList with
    | none => simp [tableResult, functionsResult] at valid
    | some functions =>
      simp only [tableResult, functionsResult] at valid
      simp at valid
      rcases valid with ⟨⟨⟨⟨⟨⟨⟨nonempty, tableMetadata⟩, tableAligned⟩,
        tableSize⟩, tableBytesExact⟩, bindingsValid⟩, ascending⟩, tableUnwindDisjoint⟩
      exact ⟨{
        tableRva := table.1
        tableBytes := table.2
        functions
        tableResolved := tableResult
        functionsResolved := functionsResult
        nonempty
        tableMetadata
        tableAligned
        tableSize
        tableBytesExact
        bindingsValid
        ascending
        tableUnwindDisjoint := by
          simp
          exact tableUnwindDisjoint }⟩


end Grass.Artifact.PE
