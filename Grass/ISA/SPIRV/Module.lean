import Grass.ISA.SPIRV.Composite
import Grass.ISA.SPIRV.Literal
import Grass.ISA.SPIRV.SourceSyntax

/-!
A bounded typed SPIR-V 1.5 module checker and word producer.  The accepted
family is the one needed by the spinning-cube vertex and fragment shaders.  It
checks its declarations and operands and refuses every unlisted opcode; it is
not a complete SPIR-V validator, CFG model, or execution semantics.

Opcode and enumerant values are from the Khronos SPIR-V 1.5.4 grammar:
https://raw.githubusercontent.com/KhronosGroup/SPIRV-Headers/1.5.4/include/spirv/unified1/spirv.core.grammar.json
-/
namespace Grass.ISA.SPIRV.Module

open SourceSyntax
abbrev Word := BitVec 32
abbrev Id := Word

inductive Storage where | input | output | private_ | pushConstant
deriving DecidableEq, Repr

inductive Ty where
  | void | bool | int (signed : Bool) | float
  | vector (element : Id) (count : Nat)
  | array (element : Id) (count : Nat)
  | struct (members : List Id)
  | pointer (storage : Storage) (pointee : Id)
  | function (result : Id)
deriving DecidableEq, Repr

inductive Stage where | vertex | fragment
deriving DecidableEq, Repr

structure Interface where
  id : Id
  pointerType : Id
  storage : Storage
  pointee : Id
deriving DecidableEq, Repr

inductive Decoration where
  | block (target : Id)
  | builtInPosition (target : Id)
  | builtInVertexIndex (target : Id)
  | location (target : Id) (location : Word)
  | memberOffset (target : Id) (member : Nat) (offset : Word)
deriving DecidableEq, Repr

structure Entry where
  stage : Stage
  functionId : Id
  name : String
  interfaceIds : List Id
  interfaces : List Interface
  pushConstants : List Interface
deriving DecidableEq, Repr

structure Output where
  words : Array Word
  entry : Entry
  idBound : Nat
  types : List (Id × Ty)
  decorations : List Decoration
deriving DecidableEq, Repr

private structure ValueInfo where
  typeId : Id
  constantNat : Option Nat := none
  variableStorage : Option Storage := none

private structure Env where
  ids : List (String × Id)
  types : List (Id × Ty) := []
  values : List (Id × ValueInfo) := []
  imports : List Id := []
  capability : Bool := false
  memoryModel : Bool := false
  entry : Option (Stage × Id × String × List Id) := none
  executionModeTargets : List Id := []
  decorations : List Decoration := []
  inFunction : Bool := false
  functionId : Option Id := none
  sawLabel : Bool := false
  sawReturn : Bool := false
  functionEnded : Bool := false

private def lookup {α β : Type} [BEq α] (key : α) : List (α × β) → Option β
  | [] => none
  | (k, v) :: rest => if key == k then some v else lookup key rest

private def atomId (env : Env) : Atom → Except String Id
  | .id name => match lookup name env.ids with
    | some id => .ok id
    | none => .error s!"unknown ID %{name}"
  | _ => .error "expected an ID operand"

private def atomWord : Atom → Except String String
  | .word text => .ok text
  | _ => .error "expected a word operand"

private def atomQuoted : Atom → Except String String
  | .quoted text => .ok text
  | _ => .error "expected a quoted operand"

private def numeric (atom : Atom) : Except String Word := do
  let text ← atomWord atom
  match Literal.parseWord32? text with
  | some word => .ok word
  | none => .error s!"invalid 32-bit unsigned decimal {text}"

private def resultId (env : Env) (statement : Statement) : Except String Id :=
  match statement.result with
  | some name => atomId env (.id name)
  | none => .error s!"{statement.opcode} requires a result ID"

private def noResult (statement : Statement) : Except String Unit :=
  if statement.result.isNone then .ok () else .error s!"{statement.opcode} cannot have a result ID"

private def storage? : String → Option (Storage × Word)
  | "Input" => some (.input, 1)
  | "Output" => some (.output, 3)
  | "Private" => some (.private_, 6)
  | "PushConstant" => some (.pushConstant, 9)
  | _ => none

private def stage? : String → Option (Stage × Word)
  | "Vertex" => some (.vertex, 0)
  | "Fragment" => some (.fragment, 4)
  | _ => none

private def instruction (opcode : Nat) (operands : List Word) : List Word :=
  BitVec.ofNat 32 ((operands.length + 1) * 65536 + opcode) :: operands

private def packedString (text : String) : List Word :=
  let bytes := text.toUTF8.data.toList ++ [0]
  let rec go : List UInt8 → List Word
    | [] => []
    | [a] => [BitVec.ofNat 32 a.toNat]
    | [a, b] => [BitVec.ofNat 32 (a.toNat + b.toNat * 256)]
    | [a, b, c] => [BitVec.ofNat 32 (a.toNat + b.toNat * 256 + c.toNat * 65536)]
    | a :: b :: c :: d :: rest =>
        BitVec.ofNat 32 (a.toNat + b.toNat * 256 + c.toNat * 65536 + d.toNat * 16777216) :: go rest
  go bytes

private def typeOf (env : Env) (id : Id) : Except String Ty :=
  match lookup id env.types with
  | some type => .ok type
  | none => .error s!"ID {id.toNat} is not a previously declared type"

private def valueOf (env : Env) (id : Id) : Except String ValueInfo :=
  match lookup id env.values with
  | some value => .ok value
  | none => .error s!"ID {id.toNat} is not a previously declared value"

private def requireType (env : Env) (id : Id) (expected : Ty) : Except String Unit := do
  let actual ← typeOf env id
  if actual = expected then .ok () else .error "type operand has the wrong kind"

private def requireValueType (env : Env) (id typeId : Id) : Except String Unit := do
  let value ← valueOf env id
  if value.typeId = typeId then .ok () else .error "value operand has the wrong type"

private def scalarType (env : Env) (id : Id) : Bool :=
  match lookup id env.types with
  | some .bool => true
  | some (.int _) => true
  | some .float => true
  | _ => false

private def compositeContext (env : Env) : Composite.Context where
  valueType id := (lookup id env.values).map ValueInfo.typeId
  vectorType id := match lookup id env.types with
    | some (.vector element count) => some (element, count)
    | _ => none
  scalarType := scalarType env

private def addType (env : Env) (id : Id) (type : Ty) : Env :=
  { env with types := (id, type) :: env.types }

private def addValue (env : Env) (id typeId : Id) (constantNat : Option Nat := none)
    (variableStorage : Option Storage := none) : Env :=
  { env with values := (id, { typeId, constantNat, variableStorage }) :: env.values }

private def typeResult (env : Env) (statement : Statement) (type : Ty)
    (opcode : Nat) (operands : List Word := []) : Except String (Env × List Word) := do
  if env.inFunction || env.functionEnded then throw "type declaration after function start"
  let id ← resultId env statement
  pure (addType env id type, instruction opcode (id :: operands))

private def wordName (atom : Atom) : Except String String := atomWord atom

private def requireBody (env : Env) (opcode : String) : Except String Unit :=
  if env.inFunction && env.sawLabel && !env.sawReturn then .ok ()
  else .error s!"misplaced {opcode}"

private def accessResultType (env : Env) (baseType : Id) (indices : List Id) : Except String Id := do
  let (.pointer _ pointee) ← typeOf env baseType | throw "OpAccessChain base is not a pointer"
  let rec descend (current : Id) : List Id → Except String Id
    | [] => .ok current
    | index :: rest => do
        let indexValue ← valueOf env index
        let .int _ ← typeOf env indexValue.typeId | throw "OpAccessChain index is not an integer"
        match ← typeOf env current with
        | .array element _ => descend element rest
        | .struct members =>
            let some n := indexValue.constantNat | throw "structure index is not constant"
            let some member := members[n]? | throw "structure index is out of bounds"
            descend member rest
        | _ => throw "OpAccessChain indexes a non-composite"
  descend pointee indices

private def step (env : Env) (statement : Statement) : Except String (Env × List Word) := do
  let op := statement.opcode
  let os := statement.operands
  if op = "OpCapability" then
    noResult statement
    if env.inFunction || env.functionEnded || env.capability then throw "duplicate or misplaced OpCapability"
    match os with
    | [.word "Shader"] => pure ({ env with capability := true }, instruction 17 [1])
    | _ => throw "only OpCapability Shader is supported"
  else if op = "OpExtInstImport" then
    if env.inFunction || env.functionEnded then throw "OpExtInstImport after function start"
    let id ← resultId env statement
    match os with
    | [name] =>
        let name ← atomQuoted name
        if name != "GLSL.std.450" then throw "unsupported extended instruction set"
        pure ({ env with imports := id :: env.imports }, instruction 11 (id :: packedString name))
    | _ => throw "bad OpExtInstImport operands"
  else if op = "OpMemoryModel" then
    noResult statement
    if env.inFunction || env.functionEnded || env.memoryModel then throw "duplicate or misplaced OpMemoryModel"
    match os with
    | [.word "Logical", .word "GLSL450"] => pure ({ env with memoryModel := true }, instruction 14 [0, 1])
    | _ => throw "only Logical GLSL450 memory model is supported"
  else if op = "OpEntryPoint" then
    noResult statement
    if env.inFunction || env.functionEnded || env.entry.isSome then throw "duplicate or misplaced OpEntryPoint"
    match os with
    | .word stageName :: function :: name :: interfaces =>
        let some (stage, stageWord) := stage? stageName | throw "unsupported execution model"
        let functionId ← atomId env function
        let name ← atomQuoted name
        let interfaceIds ← interfaces.mapM (atomId env)
        pure ({ env with entry := some (stage, functionId, name, interfaceIds) },
          instruction 15 ([stageWord, functionId] ++ packedString name ++ interfaceIds))
    | _ => throw "bad OpEntryPoint operands"
  else if op = "OpExecutionMode" then
    noResult statement
    if env.inFunction || env.functionEnded then throw "misplaced OpExecutionMode"
    match os with
    | [target, .word "OriginUpperLeft"] =>
        let target ← atomId env target
        pure ({ env with executionModeTargets := target :: env.executionModeTargets }, instruction 16 [target, 7])
    | _ => throw "only OriginUpperLeft execution mode is supported"
  else if op = "OpName" then
    noResult statement
    if env.inFunction || env.functionEnded then throw "misplaced OpName"
    match os with
    | [target, name] =>
        let target ← atomId env target; let name ← atomQuoted name
        pure (env, instruction 5 (target :: packedString name))
    | _ => throw "bad OpName operands"
  else if op = "OpDecorate" then
    noResult statement
    if env.inFunction || env.functionEnded then throw "misplaced OpDecorate"
    match os with
    | [target, .word "Block"] =>
        let target ← atomId env target
        pure ({ env with decorations := .block target :: env.decorations }, instruction 71 [target, 2])
    | [target, .word "BuiltIn", .word builtin] =>
        let target ← atomId env target
        let value ← match builtin with | "Position" => pure 0 | "VertexIndex" => pure 42 | _ => throw "unsupported BuiltIn"
        let decoration := if builtin = "Position" then .builtInPosition target else .builtInVertexIndex target
        pure ({ env with decorations := decoration :: env.decorations }, instruction 71 [target, 11, value])
    | [target, .word "Location", location] =>
        let target ← atomId env target; let location ← numeric location
        pure ({ env with decorations := .location target location :: env.decorations }, instruction 71 [target, 30, location])
    | _ => throw "unsupported OpDecorate"
  else if op = "OpMemberDecorate" then
    noResult statement
    if env.inFunction || env.functionEnded then throw "misplaced OpMemberDecorate"
    match os with
    | [target, member, .word "Offset", offset] =>
        let target ← atomId env target; let member ← numeric member; let offset ← numeric offset
        pure ({ env with decorations := .memberOffset target member.toNat offset :: env.decorations },
          instruction 72 [target, member, 35, offset])
    | _ => throw "unsupported OpMemberDecorate"
  else if op = "OpTypeVoid" then
    if os.isEmpty then typeResult env statement .void 19 else throw "OpTypeVoid has operands"
  else if op = "OpTypeBool" then
    if os.isEmpty then typeResult env statement .bool 20 else throw "OpTypeBool has operands"
  else if op = "OpTypeInt" then
    match os with
    | [width, signed] =>
        let width ← numeric width; let signed ← numeric signed
        if width != 32 || (signed != 0 && signed != 1) then throw "only 32-bit integer types are supported"
        typeResult env statement (.int (signed == 1)) 21 [width, signed]
    | _ => throw "bad OpTypeInt operands"
  else if op = "OpTypeFloat" then
    match os with
    | [width] =>
        let width ← numeric width
        if width != 32 then throw "only float32 is supported"
        typeResult env statement .float 22 [width]
    | _ => throw "bad OpTypeFloat operands"
  else if op = "OpTypeVector" then
    match os with
    | [element, count] =>
        let element ← atomId env element; let count ← numeric count
        if !scalarType env element || count.toNat < 2 || 4 < count.toNat then throw "unsupported vector type"
        typeResult env statement (.vector element count.toNat) 23 [element, count]
    | _ => throw "bad OpTypeVector operands"
  else if op = "OpTypeArray" then
    match os with
    | [element, length] =>
        let element ← atomId env element; let _ ← typeOf env element
        let length ← atomId env length; let lengthValue ← valueOf env length
        let .int false ← typeOf env lengthValue.typeId | throw "array length is not uint32"
        let some count := lengthValue.constantNat | throw "array length is not constant"
        if count = 0 then throw "zero-length arrays are unsupported"
        typeResult env statement (.array element count) 28 [element, length]
    | _ => throw "bad OpTypeArray operands"
  else if op = "OpTypeStruct" then
    let members ← os.mapM (atomId env)
    for member in members do let _ ← typeOf env member
    typeResult env statement (.struct members) 30 members
  else if op = "OpTypePointer" then
    match os with
    | [.word storageName, pointee] =>
        let some (storage, storageWord) := storage? storageName | throw "unsupported storage class"
        let pointee ← atomId env pointee; let _ ← typeOf env pointee
        typeResult env statement (.pointer storage pointee) 32 [storageWord, pointee]
    | _ => throw "bad OpTypePointer operands"
  else if op = "OpTypeFunction" then
    match os with
    | [result] =>
        let result ← atomId env result; requireType env result .void
        typeResult env statement (.function result) 33 [result]
    | _ => throw "only nullary function types are supported"
  else if op = "OpConstant" then
    if env.inFunction || env.functionEnded then throw "misplaced OpConstant"
    let id ← resultId env statement
    match os with
    | [typeAtom, literal] =>
        let typeId ← atomId env typeAtom; let type ← typeOf env typeId; let text ← atomWord literal
        let (word, natural) ← match type with
          | .int signed => match Literal.int32? signed text with
            | some word => pure (word, some word.toNat)
            | none => throw "invalid typed int32 constant"
          | .float => match Literal.float32Exact? text with
            | some word => pure (word, none)
            | none => throw "inexact or invalid float32 constant"
          | _ => throw "OpConstant requires int32 or float32"
        pure (addValue env id typeId natural, instruction 43 [typeId, id, word])
    | _ => throw "bad OpConstant operands"
  else if op = "OpConstantComposite" then
    if env.inFunction || env.functionEnded then throw "misplaced OpConstantComposite"
    let id ← resultId env statement
    match os with
    | typeAtom :: constituents =>
        let typeId ← atomId env typeAtom; let constituentIds ← constituents.mapM (atomId env)
        let expected ← match ← typeOf env typeId with
          | .vector element count => pure (element, count)
          | .array element count => pure (element, count)
          | .struct members =>
              if members.length != constituentIds.length then throw "wrong composite constituent count"
              for pair in members.zip constituentIds do requireValueType env pair.2 pair.1
              pure (typeId, 0)
          | _ => throw "constant composite requires a composite type"
        if expected.2 != 0 then
          if constituentIds.length != expected.2 then throw "wrong composite constituent count"
          for constituent in constituentIds do requireValueType env constituent expected.1
        pure (addValue env id typeId, instruction 44 (typeId :: id :: constituentIds))
    | _ => throw "bad OpConstantComposite operands"
  else if op = "OpVariable" then
    let id ← resultId env statement
    match os with
    | typeAtom :: .word storageName :: initializer =>
        let typeId ← atomId env typeAtom
        let some (storage, storageWord) := storage? storageName | throw "unsupported storage class"
        let .pointer pointerStorage pointee ← typeOf env typeId | throw "OpVariable type is not a pointer"
        if pointerStorage != storage then throw "OpVariable storage class disagrees with pointer"
        if env.inFunction || env.functionEnded then throw "misplaced OpVariable"
        let initWords ← match initializer with
          | [] => pure []
          | [initial] =>
              let initial ← atomId env initial; requireValueType env initial pointee; pure [initial]
          | _ => throw "bad OpVariable initializer"
        pure (addValue env id typeId none (some storage), instruction 59 ([typeId, id, storageWord] ++ initWords))
    | _ => throw "bad OpVariable operands"
  else if op = "OpFunction" then
    if env.inFunction || env.functionEnded then throw "only one function is supported"
    let id ← resultId env statement
    match os with
    | [resultType, .word "None", functionType] =>
        let resultType ← atomId env resultType; requireType env resultType .void
        let functionType ← atomId env functionType; requireType env functionType (.function resultType)
        pure ({ (addValue env id resultType) with inFunction := true, functionId := some id }, instruction 54 [resultType, id, 0, functionType])
    | _ => throw "bad OpFunction operands"
  else if op = "OpLabel" then
    if !env.inFunction || env.sawLabel then throw "expected exactly one function label"
    let id ← resultId env statement
    if !os.isEmpty then throw "OpLabel has operands"
    pure ({ (addValue env id 0) with sawLabel := true }, instruction 248 [id])
  else if op = "OpLoad" then
    requireBody env op
    let id ← resultId env statement
    match os with
    | [typeAtom, pointerAtom] =>
        let typeId ← atomId env typeAtom; let pointer ← atomId env pointerAtom
        let pointerValue ← valueOf env pointer
        let .pointer _ pointee ← typeOf env pointerValue.typeId | throw "OpLoad operand is not a pointer"
        if pointee != typeId then throw "OpLoad result type disagrees with pointee"
        pure (addValue env id typeId, instruction 61 [typeId, id, pointer])
    | _ => throw "bad OpLoad operands"
  else if op = "OpStore" then
    noResult statement
    requireBody env op
    match os with
    | [pointerAtom, objectAtom] =>
        let pointer ← atomId env pointerAtom; let object ← atomId env objectAtom
        let pointerValue ← valueOf env pointer
        let .pointer _ pointee ← typeOf env pointerValue.typeId | throw "OpStore target is not a pointer"
        requireValueType env object pointee
        pure (env, instruction 62 [pointer, object])
    | _ => throw "bad OpStore operands"
  else if op = "OpAccessChain" then
    requireBody env op
    let id ← resultId env statement
    match os with
    | typeAtom :: baseAtom :: indexAtoms =>
        if indexAtoms.isEmpty then throw "empty OpAccessChain is unsupported"
        let typeId ← atomId env typeAtom; let base ← atomId env baseAtom
        let baseInfo ← valueOf env base; let indices ← indexAtoms.mapM (atomId env)
        let derived ← accessResultType env baseInfo.typeId indices
        let .pointer resultStorage resultPointee ← typeOf env typeId | throw "OpAccessChain result type is not pointer"
        let .pointer baseStorage _ ← typeOf env baseInfo.typeId | throw "OpAccessChain base type is not pointer"
        if resultStorage != baseStorage || resultPointee != derived then throw "OpAccessChain result pointer is mistyped"
        pure (addValue env id typeId, instruction 65 (typeId :: id :: base :: indices))
    | _ => throw "bad OpAccessChain operands"
  else if op = "OpCompositeExtract" then
    requireBody env op
    let id ← resultId env statement
    match os with
    | [typeAtom, compositeAtom, indexAtom] =>
        let resultType ← atomId env typeAtom
        let composite ← atomId env compositeAtom
        let index ← numeric indexAtom
        let operands : Composite.Extract := { resultType, result := id, composite, index }
        if _h : operands.check (compositeContext env) then
          pure (addValue env id operands.resultType, (Composite.Instruction.extract operands).encode)
        else throw "inapplicable OpCompositeExtract"
    | _ => throw "bad OpCompositeExtract operands"
  else if op = "OpCompositeConstruct" then
    requireBody env op
    let id ← resultId env statement
    match os with
    | [typeAtom, x, y, z, w] =>
        let resultType ← atomId env typeAtom
        let x ← atomId env x; let y ← atomId env y; let z ← atomId env z; let w ← atomId env w
        let operands : Composite.Construct4 := { resultType, result := id, x, y, z, w }
        if _h : operands.check (compositeContext env) then
          pure (addValue env id operands.resultType, (Composite.Instruction.construct4 operands).encode)
        else throw "inapplicable OpCompositeConstruct"
    | _ => throw "only four-constituent OpCompositeConstruct is supported"
  else if op = "OpFAdd" || op = "OpFSub" || op = "OpFMul" || op = "OpFDiv" then
    requireBody env op
    let id ← resultId env statement
    match os with
    | [typeAtom, xAtom, yAtom] =>
        let typeId ← atomId env typeAtom; let x ← atomId env xAtom; let y ← atomId env yAtom
        let type ← typeOf env typeId
        let admissible := type == .float || match type with | .vector element _ => (lookup element env.types) == some .float | _ => false
        if !admissible then throw "floating arithmetic requires float32 scalar/vector"
        requireValueType env x typeId; requireValueType env y typeId
        let opcode := if op = "OpFAdd" then 129 else if op = "OpFSub" then 131 else if op = "OpFMul" then 133 else 136
        pure (addValue env id typeId, instruction opcode [typeId, id, x, y])
    | _ => throw "bad floating arithmetic operands"
  else if op = "OpVectorTimesScalar" then
    requireBody env op
    let id ← resultId env statement
    match os with
    | [typeAtom, vectorAtom, scalarAtom] =>
        let typeId ← atomId env typeAtom; let vector ← atomId env vectorAtom; let scalar ← atomId env scalarAtom
        let .vector element _ ← typeOf env typeId | throw "OpVectorTimesScalar result is not vector"
        requireType env element .float; requireValueType env vector typeId; requireValueType env scalar element
        pure (addValue env id typeId, instruction 142 [typeId, id, vector, scalar])
    | _ => throw "bad OpVectorTimesScalar operands"
  else if op = "OpExtInst" then
    requireBody env op
    let id ← resultId env statement
    match os with
    | [typeAtom, setAtom, .word operation, argumentAtom] =>
        let typeId ← atomId env typeAtom; requireType env typeId .float
        let set ← atomId env setAtom
        if !env.imports.contains set then throw "unknown extended instruction set"
        let extOpcode ← match operation with | "Sin" => pure 13 | "Cos" => pure 14 | _ => throw "unsupported GLSL450 instruction"
        let argument ← atomId env argumentAtom; requireValueType env argument typeId
        pure (addValue env id typeId, instruction 12 [typeId, id, set, extOpcode, argument])
    | _ => throw "bad OpExtInst operands"
  else if op = "OpReturn" then
    noResult statement
    if !env.inFunction || !env.sawLabel || env.sawReturn || !os.isEmpty then throw "misplaced OpReturn"
    pure ({ env with sawReturn := true }, instruction 253 [])
  else if op = "OpFunctionEnd" then
    noResult statement
    if !env.inFunction || !env.sawReturn || !os.isEmpty then throw "incomplete function before OpFunctionEnd"
    pure ({ env with inFunction := false, functionEnded := true }, instruction 56 [])
  else throw s!"unsupported SPIR-V opcode {op}"

private def assignIds (statements : List Statement) : Except String (List (String × Id)) := do
  let rec go (next : Nat) (ids : List (String × Id)) : List Statement → Except String (List (String × Id))
    | [] => pure ids.reverse
    | statement :: rest => match statement.result with
      | none => go next ids rest
      | some name => do
          if name.isEmpty then throw "empty result ID name" else pure ()
          if (lookup name ids).isSome then throw ("duplicate result ID %" ++ name) else pure ()
          if next ≥ (2 ^ 32 - 1) then throw "SPIR-V ID bound exceeds 32 bits" else pure ()
          go (next + 1) ((name, BitVec.ofNat 32 next) :: ids) rest
  go 1 [] statements

private def finish (env : Env) (bodyWords : List Word) : Except String Output := do
  if !env.capability then throw "missing OpCapability Shader" else pure ()
  if !env.memoryModel then throw "missing Logical GLSL450 OpMemoryModel" else pure ()
  if env.inFunction || !env.functionEnded then throw "missing complete single-block function" else pure ()
  let some (stage, functionId, name, interfaces) := env.entry | throw "missing OpEntryPoint"
  if env.functionId != some functionId then throw "entry point does not name the defined function" else pure ()
  for target in env.executionModeTargets do
    if target != functionId then throw "execution mode targets a non-entry function" else pure ()
  match stage with
  | .vertex => if !env.executionModeTargets.isEmpty then throw "OriginUpperLeft is not a vertex execution mode" else pure ()
  | .fragment => if env.executionModeTargets != [functionId] then throw "fragment entry requires one OriginUpperLeft mode" else pure ()
  for decoration in env.decorations do
    match decoration with
    | .block target =>
        let .struct _ ← typeOf env target | throw "Block decoration target is not a structure type"
    | .memberOffset target member _ =>
        let .struct members ← typeOf env target | throw "member Offset target is not a structure type"
        if member < members.length then pure () else throw "member Offset index is out of bounds"
    | .builtInPosition target =>
        if stage != .vertex || !interfaces.contains target then throw "Position BuiltIn is not a vertex entry interface" else pure ()
        let info ← valueOf env target
        let some .output := info.variableStorage | throw "Position BuiltIn is not an Output variable"
        let .pointer .output pointee ← typeOf env info.typeId | throw "Position BuiltIn has wrong pointer storage"
        let .vector element 4 ← typeOf env pointee | throw "Position BuiltIn is not vec4"
        requireType env element .float
    | .builtInVertexIndex target =>
        if stage != .vertex || !interfaces.contains target then throw "VertexIndex BuiltIn is not a vertex entry interface" else pure ()
        let info ← valueOf env target
        let some .input := info.variableStorage | throw "VertexIndex BuiltIn is not an Input variable"
        let .pointer .input pointee ← typeOf env info.typeId | throw "VertexIndex BuiltIn has wrong pointer storage"
        requireType env pointee (.int true)
    | .location target _ =>
        if !interfaces.contains target then throw "Location target is not an entry interface" else pure ()
        let info ← valueOf env target
        let some storage := info.variableStorage | throw "Location target is not a variable"
        if storage != .input && storage != .output then throw "Location target has wrong storage" else pure ()
        let .pointer _ pointee ← typeOf env info.typeId | throw "Location target is not a pointer"
        match ← typeOf env pointee with
        | .float => pure ()
        | .vector element count =>
            requireType env element .float
            if 2 ≤ count && count ≤ 4 then pure () else throw "Location vector width is unsupported"
        | _ => throw "Location target does not point to float scalar/vector"
  let mut declarations := []
  let mut pushes := []
  for id in interfaces do
    let info ← valueOf env id
    let some storage := info.variableStorage | throw "entry interface is not a global variable"
    let .pointer pointerStorage pointee ← typeOf env info.typeId | throw "entry interface has non-pointer type"
    if pointerStorage != storage then throw "entry interface pointer storage mismatch" else pure ()
    let declaration : Interface := { id, pointerType := info.typeId, storage, pointee }
    declarations := declaration :: declarations
    if storage == .pushConstant then pushes := declaration :: pushes else pure ()
  for push in pushes do
    let .struct members ← typeOf env push.pointee | throw "PushConstant variable does not point to a structure"
    if !env.decorations.contains (.block push.pointee) then throw "PushConstant structure lacks Block decoration" else pure ()
    for member in List.range members.length do
      let hasOffset := env.decorations.any (fun decoration => match decoration with
        | .memberOffset target index _ => target == push.pointee && index == member
        | _ => false)
      if !hasOffset then throw "PushConstant structure member lacks Offset decoration" else pure ()
  let bound := env.ids.length + 1
  let header : List Word := [0x07230203, 0x00010500, 0, BitVec.ofNat 32 bound, 0]
  let entry : Entry := ⟨stage, functionId, name, interfaces, declarations.reverse, pushes.reverse⟩
  pure ⟨(header ++ bodyWords).toArray, entry, bound, env.types.reverse, env.decorations.reverse⟩

/-- Deterministically assigns every result ID, then checks and encodes the same statements. -/
def compile (statements : List Statement) : Except String Output := do
  for statement in statements do
    if statement.operands.length ≥ 65530 then throw "instruction operand count exceeds SPIR-V word count" else pure ()
    for atom in statement.operands do
      match atom with
      | .quoted text =>
          if text.contains (Char.ofNat 0) then throw "SPIR-V literal string contains embedded NUL" else pure ()
          if text.toUTF8.size / 4 ≥ 65530 then throw "SPIR-V literal string is too long" else pure ()
      | _ => pure ()
  let ids ← assignIds statements
  let rec loop (env : Env) (words : List Word) : List Statement → Except String Output
    | [] => finish env words
    | statement :: rest => do
        let (env, encoded) ← step env statement
        if encoded.length > 65535 then throw "encoded instruction exceeds SPIR-V word count" else pure ()
        loop env (words ++ encoded) rest
  loop { ids } [] statements

/-- A successful witness binds exact emitted words and entry metadata to its source AST. -/
structure Checked where
  private mk ::
  source : List Statement
  output : Output
  checked : compile source = .ok output

def check (source : List Statement) : Except String Checked :=
  match h : compile source with
  | .error error => .error error
  | .ok output => .ok ⟨source, output, h⟩

theorem Checked.words_exact (checked : Checked) :
    compile checked.source = .ok checked.output := checked.checked

end Grass.ISA.SPIRV.Module
