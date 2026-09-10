/-!
# Bounded SPIR-V vector composite instructions

This module models the two composite forms used by the spinning-cube shader:
one-index vector `OpCompositeExtract` and four-scalar vector
`OpCompositeConstruct`.  It is deliberately operand-local: the caller supplies
the relevant SPIR-V type and value-ID environment, and decoding checks it.
The context is an operand-local input: this module does not establish the
module header's ID bound, context faithfulness, module-wide uniqueness,
dominance, or full SPIR-V validation.

The binary layouts and opcodes come from the Khronos SPIR-V 1.5 grammar and
specification:

* https://raw.githubusercontent.com/KhronosGroup/SPIRV-Headers/1.5.4/include/spirv/unified1/spirv.core.grammar.json
* https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html#OpCompositeConstruct
* https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html#OpCompositeExtract

The semantic lane type is opaque.  Thus the laws preserve the selected value,
without asserting floating-point admissibility or bit-level `f32` behavior.
-/

namespace Grass.ISA.SPIRV.Composite

abbrev Word := BitVec 32
abbrev Id := Word

/-- The operand-local facts needed to type-check this bounded family. -/
structure Context where
  /-- Type ID assigned to each value ID in the surrounding module. -/
  valueType : Id → Option Id
  /-- Component type and lane count assigned to each vector type ID. -/
  vectorType : Id → Option (Id × Nat)
  /-- Whether a type ID is a scalar type in this local environment. -/
  scalarType : Id → Bool

/-- A single-index vector extraction. -/
structure Extract where
  resultType : Id
  result : Id
  composite : Id
  index : Word
deriving DecidableEq, Repr

/-- The four scalar constituents of the cube shader's vector construction. -/
structure Construct4 where
  resultType : Id
  result : Id
  x : Id
  y : Id
  z : Id
  w : Id
deriving DecidableEq, Repr

inductive Instruction where
  | extract (operands : Extract)
  | construct4 (operands : Construct4)
deriving DecidableEq, Repr

def Instruction.resultId : Instruction → Id
  | .extract operands => operands.result
  | .construct4 operands => operands.result

/-- Executable applicability check for the supported one-level vector extraction. -/
def Extract.check (context : Context) (operands : Extract) : Bool :=
  (operands.resultType != 0) && (operands.result != 0) &&
  (operands.composite != 0) && (operands.result != operands.composite) &&
  (!context.scalarType operands.result) &&
  (context.vectorType operands.result == none) &&
  context.scalarType operands.resultType &&
  (context.vectorType operands.resultType == none) &&
  (context.valueType operands.result == none) &&
  match context.valueType operands.composite with
  | none => false
  | some vectorType =>
      match context.vectorType vectorType with
      | none => false
      | some (laneType, laneCount) =>
          (!context.scalarType vectorType) &&
          (laneType == operands.resultType) && decide (2 ≤ laneCount) &&
          decide (laneCount ≤ 4) && decide (operands.index.toNat < laneCount)

/-- Checked applicability for exactly four scalar constituents. -/
def Construct4.check (context : Context) (operands : Construct4) : Bool :=
  (operands.resultType != 0) && (operands.result != 0) &&
  (operands.x != 0) && (operands.y != 0) && (operands.z != 0) && (operands.w != 0) &&
  (operands.result != operands.x) && (operands.result != operands.y) &&
  (operands.result != operands.z) && (operands.result != operands.w) &&
  (!context.scalarType operands.result) &&
  (context.vectorType operands.result == none) &&
  (context.valueType operands.result == none) &&
  match context.vectorType operands.resultType with
  | none => false
  | some (laneType, laneCount) =>
      (!context.scalarType operands.resultType) && context.scalarType laneType &&
      (context.vectorType laneType == none) &&
      (laneCount == 4) &&
      (context.valueType operands.x == some laneType) &&
      (context.valueType operands.y == some laneType) &&
      (context.valueType operands.z == some laneType) &&
      (context.valueType operands.w == some laneType)

def Instruction.Applicable (context : Context) : Instruction → Prop
  | .extract operands => operands.check context = true
  | .construct4 operands => operands.check context = true

instance (context : Context) (instruction : Instruction) :
    Decidable (instruction.Applicable context) := by
  cases instruction <;> simp only [Instruction.Applicable] <;> infer_instance

def extractHeader : Word := 0x00050051
def construct4Header : Word := 0x00070050

/-- Exact words for the supported SPIR-V instruction, including its header. -/
def Instruction.encode : Instruction → List Word
  | .extract operands =>
      [extractHeader, operands.resultType, operands.result, operands.composite, operands.index]
  | .construct4 operands =>
      [construct4Header, operands.resultType, operands.result,
        operands.x, operands.y, operands.z, operands.w]

/-- A checked instruction packages decoder-established typing and bounds. -/
abbrev Checked (context : Context) := { instruction : Instruction // instruction.Applicable context }

inductive Error where
  | empty
  | unsupportedHeader (header : Word)
  | truncatedExtract
  | truncatedConstruct4
  | inapplicable (instruction : Instruction)
deriving DecidableEq, Repr

structure Result (context : Context) where
  checked : Checked context
  rest : List Word
deriving DecidableEq

/-- Decode exactly one bounded instruction, retaining the untouched word suffix. -/
def decode (context : Context) (words : List Word) : Except Error (Result context) :=
  match words with
  | [] => .error .empty
  | header :: tail =>
      if header = extractHeader then
        match tail with
        | resultType :: result :: composite :: index :: rest =>
            let instruction := .extract { resultType, result, composite, index }
            if h : instruction.Applicable context then
              .ok ⟨⟨instruction, h⟩, rest⟩
            else .error (.inapplicable instruction)
        | _ => .error .truncatedExtract
      else if header = construct4Header then
        match tail with
        | resultType :: result :: x :: y :: z :: w :: rest =>
            let instruction := .construct4 { resultType, result, x, y, z, w }
            if h : instruction.Applicable context then
              .ok ⟨⟨instruction, h⟩, rest⟩
            else .error (.inapplicable instruction)
        | _ => .error .truncatedConstruct4
      else .error (.unsupportedHeader header)

/-- Successful decoding identifies the exact consumed prefix and suffix. -/
theorem decode_ok_framing {context : Context} {words : List Word} {result : Result context}
    (h : decode context words = .ok result) :
    words = result.checked.val.encode ++ result.rest := by
  simp only [decode] at h
  split at h <;> try contradiction
  next header tail heq =>
    split at h
    next hextract =>
      split at h <;> try contradiction
      next resultType resultId composite index rest htail =>
        split at h <;> try contradiction
        next happlicable =>
          simp only [Except.ok.injEq] at h
          subst result
          simp [Instruction.encode, extractHeader, hextract]
    next hnotExtract =>
      split at h
      next hconstruct =>
        split at h <;> try contradiction
        next resultType resultId x y z w rest htail =>
          split at h <;> try contradiction
          next happlicable =>
            simp only [Except.ok.injEq] at h
            subst result
            simp [Instruction.encode, construct4Header, hconstruct]
      next hnotConstruct => contradiction

/-- Encoding any applicable supported instruction round-trips with every suffix. -/
theorem decode_encode_append (context : Context) (checked : Checked context)
    (suffix : List Word) :
    (decode context (checked.val.encode ++ suffix)).map
      (fun result => (result.checked.val, result.rest)) = .ok (checked.val, suffix) := by
  obtain ⟨instruction, applicable⟩ := checked
  cases instruction with
  | extract operands =>
      change Extract.check context operands = true at applicable
      simp [Instruction.encode, decode, extractHeader, Instruction.Applicable, applicable]
      rfl
  | construct4 operands =>
      change Construct4.check context operands = true at applicable
      simp [Instruction.encode, decode, extractHeader, construct4Header,
        Instruction.Applicable, applicable]
      rfl

variable {α : Type} {context : Context}

/-- Operand-local semantic values.  `α` may be a symbolic scalar domain. -/
inductive Value (α : Type) where
  | scalar (value : α)
  | vector (lanes : List α)
deriving DecidableEq, Repr

abbrev Store (α : Type) := Id → Option (Value α)

/-- Runtime values agree with every declared scalar/vector value used locally. -/
def Store.Typed (context : Context) (store : Store α) : Prop :=
  ∀ id,
    match context.valueType id with
    | none => store id = none
    | some typeId =>
        match context.vectorType typeId with
        | some (_, laneCount) =>
            ∃ lanes, store id = some (.vector lanes) ∧ lanes.length = laneCount
        | none =>
            if context.scalarType typeId then
              ∃ value, store id = some (.scalar value)
            else False

/-- Extend the local ID environment with the fresh result of one instruction. -/
def Context.withResult (context : Context) (result typeId : Id) : Context where
  valueType id := if id = result then some typeId else context.valueType id
  vectorType := context.vectorType
  scalarType := context.scalarType

/-- The supported transfer updates only the result ID. -/
def transfer (instruction : Instruction) (before : Store α) : Option (Store α) :=
  match instruction with
  | .extract operands =>
      match before operands.composite with
      | some (.vector lanes) => do
          let lane ← lanes[operands.index.toNat]?
          pure (fun id => if id = operands.result then some (.scalar lane) else before id)
      | _ => none
  | .construct4 operands =>
      match before operands.x, before operands.y, before operands.z, before operands.w with
      | some (.scalar x), some (.scalar y), some (.scalar z), some (.scalar w) =>
          some (fun id => if id = operands.result then some (.vector [x, y, z, w]) else before id)
      | _, _, _, _ => none

def Result.effect (result : Result context) (before : Store α) : Option (Store α) :=
  transfer result.checked.val before

/-- A successful encoded instruction denotes the same typed transfer packaged by its result. -/
theorem decode_ok_effect {context : Context} {words : List Word} {result : Result context}
    (h : decode context words = .ok result) (before : Store α) :
    words = result.checked.val.encode ++ result.rest ∧
      result.effect before = transfer result.checked.val before :=
  ⟨decode_ok_framing h, rfl⟩

/-- Extraction writes exactly the selected runtime lane. -/
theorem transfer_extract_result (operands : Extract) (before : Store α)
    (lanes : List α) (lane : α)
    (hvector : before operands.composite = some (.vector lanes))
    (hlane : lanes[operands.index.toNat]? = some lane) :
    (transfer (.extract operands) before).map (fun after => after operands.result) =
      some (some (.scalar lane)) := by
  simp [transfer, hvector, hlane]

/-- Construction writes its four scalar operands in SPIR-V operand order. -/
theorem transfer_construct4_result (operands : Construct4) (before : Store α)
    (x y z w : α)
    (hx : before operands.x = some (.scalar x))
    (hy : before operands.y = some (.scalar y))
    (hz : before operands.z = some (.scalar z))
    (hw : before operands.w = some (.scalar w)) :
    (transfer (.construct4 operands) before).map (fun after => after operands.result) =
      some (some (.vector [x, y, z, w])) := by
  simp [transfer, hx, hy, hz, hw]

/-- A checked extraction over a typed store is total and extends the context
with a correctly typed scalar result. -/
theorem checked_extract_total (context : Context) (operands : Extract)
    (applicable : (Instruction.extract operands).Applicable context)
    {before : Store α} (typed : before.Typed context) :
    ∃ after lane,
      transfer (.extract operands) before = some after ∧
      after operands.result = some (.scalar lane) ∧
      after.Typed (context.withResult operands.result operands.resultType) := by
  change Extract.check context operands = true at applicable
  cases hsource : context.valueType operands.composite with
  | none => simp [Extract.check, hsource] at applicable
  | some vectorType =>
      cases hvectorType : context.vectorType vectorType with
      | none => simp [Extract.check, hsource, hvectorType] at applicable
      | some pair =>
          obtain ⟨laneType, laneCount⟩ := pair
          simp [Extract.check, hsource, hvectorType] at applicable
          obtain ⟨hleft, _, hindex⟩ := applicable
          have hscalar := hleft.1.1.2
          have hresultNoVector := hleft.1.2
          have htypedSource := typed operands.composite
          simp [hsource, hvectorType] at htypedSource
          obtain ⟨lanes, hlanes, hlength⟩ := htypedSource
          have hindexLength : operands.index.toNat < lanes.length := by
            rw [hlength]
            exact hindex
          let lane := lanes[operands.index.toNat]
          have hget : lanes[operands.index.toNat]? = some lane := by
            simp [lane, hindexLength]
          let after : Store α := fun id =>
            if id = operands.result then some (.scalar lane) else before id
          refine ⟨after, lane, ?_, by simp [after], ?_⟩
          · simp [transfer, hlanes, hget, after]
          · intro id
            by_cases hid : id = operands.result
            · subst id
              simp [Context.withResult, after, hresultNoVector, hscalar]
            · have hvalueType :
                  (context.withResult operands.result operands.resultType).valueType id =
                    context.valueType id := by simp [Context.withResult, hid]
              rw [hvalueType]
              have hafter : after id = before id := by simp [after, hid]
              rw [hafter]
              exact typed id

/-- A checked four-lane construction over a typed store is total and extends
the context with a correctly typed vector result in operand order. -/
theorem checked_construct4_total (context : Context) (operands : Construct4)
    (applicable : (Instruction.construct4 operands).Applicable context)
    {before : Store α} (typed : before.Typed context) :
    ∃ after x y z w,
      transfer (.construct4 operands) before = some after ∧
      after operands.result = some (.vector [x, y, z, w]) ∧
      after.Typed (context.withResult operands.result operands.resultType) := by
  change Construct4.check context operands = true at applicable
  cases hresultType : context.vectorType operands.resultType with
  | none => simp [Construct4.check, hresultType] at applicable
  | some pair =>
      obtain ⟨laneType, laneCount⟩ := pair
      simp [Construct4.check, hresultType] at applicable
      obtain ⟨_, hright⟩ := applicable
      obtain ⟨⟨⟨⟨⟨⟨⟨hresultNotScalar, hlaneScalar⟩, hlaneNoVector⟩,
        hlaneCount⟩, hxType⟩, hyType⟩, hzType⟩, hwType⟩ := hright
      have htx := typed operands.x
      have hty := typed operands.y
      have htz := typed operands.z
      have htw := typed operands.w
      rw [hxType] at htx
      rw [hyType] at hty
      rw [hzType] at htz
      rw [hwType] at htw
      simp [hlaneNoVector, hlaneScalar] at htx hty htz htw
      obtain ⟨x, hx⟩ := htx
      obtain ⟨y, hy⟩ := hty
      obtain ⟨z, hz⟩ := htz
      obtain ⟨w, hw⟩ := htw
      let after : Store α := fun id =>
        if id = operands.result then some (.vector [x, y, z, w]) else before id
      refine ⟨after, x, y, z, w, ?_, by simp [after], ?_⟩
      · simp [transfer, hx, hy, hz, hw, after]
      · intro id
        by_cases hid : id = operands.result
        · subst id
          simp [Context.withResult, after, hresultType, hlaneCount]
        · have hvalueType :
              (context.withResult operands.result operands.resultType).valueType id =
                context.valueType id := by simp [Context.withResult, hid]
          rw [hvalueType]
          have hafter : after id = before id := by simp [after, hid]
          rw [hafter]
          exact typed id

/-- Either supported transfer leaves every ID other than its result unchanged. -/
theorem transfer_frame {instruction : Instruction} {before after : Store α}
    (htransfer : transfer instruction before = some after)
    {id : Id} (hne : id ≠ instruction.resultId) :
    after id = before id := by
  cases instruction with
  | extract operands =>
      simp only [Instruction.resultId] at hne
      simp only [transfer] at htransfer
      split at htransfer <;> try contradiction
      next lanes hvector =>
        cases hlane : lanes[operands.index.toNat]? with
        | none => simp [hlane] at htransfer
        | some lane =>
            simp [hlane] at htransfer
            subst after
            simp [hne]
  | construct4 operands =>
      simp only [Instruction.resultId] at hne
      simp only [transfer] at htransfer
      split at htransfer <;> try contradiction
      next x y z w hx hy hz hw =>
        simp only [Option.some.injEq] at htransfer
        subst after
        simp [hne]

end Grass.ISA.SPIRV.Composite
