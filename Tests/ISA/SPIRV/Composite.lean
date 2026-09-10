import Grass.ISA.SPIRV.Composite

namespace Tests.ISA.SPIRV.Composite

open Grass.ISA.SPIRV.Composite

def floatType : Id := 1
def vec3Type : Id := 2
def vec4Type : Id := 3
def source3 : Id := 10
def xId : Id := 11
def yId : Id := 12
def zId : Id := 13
def wId : Id := 14
def output4 : Id := 15
def extracted : Id := 16

def context : Context where
  valueType id :=
    if id = source3 then some vec3Type
    else if id = xId ∨ id = yId ∨ id = zId ∨ id = wId then some floatType
    else none
  vectorType id :=
    if id = vec3Type then some (floatType, 3)
    else if id = vec4Type then some (floatType, 4)
    else none
  scalarType id := id == floatType

def extract1 : Instruction :=
  .extract { resultType := floatType, result := extracted, composite := source3, index := 1 }

def construct4 : Instruction :=
  .construct4
    { resultType := vec4Type, result := output4, x := xId, y := yId, z := zId, w := wId }

example : extract1.Applicable context := by decide
example : construct4.Applicable context := by decide

example :
    decode context (extract1.encode ++ [0xdeadbeef]) =
      .ok ⟨⟨extract1, by decide⟩, [0xdeadbeef]⟩ := by rfl

example :
    decode context (construct4.encode ++ [0xdeadbeef]) =
      .ok ⟨⟨construct4, by decide⟩, [0xdeadbeef]⟩ := by rfl

-- Wrong opcode and wrong word count are both rejected by the exact header.
example : decode context (0x00050052 :: extract1.encode.tail) =
    .error (.unsupportedHeader 0x00050052) := by rfl
example : decode context (0x00060051 :: extract1.encode.tail) =
    .error (.unsupportedHeader 0x00060051) := by rfl

-- The same shape is rejected for an out-of-range lane.
example :
    decode context [extractHeader, floatType, extracted, source3, 3] =
      .error (.inapplicable
        (.extract { resultType := floatType, result := extracted, composite := source3, index := 3 })) := by
  rfl

-- A wrong result type and an unknown operand ID are rejected from the context.
example :
    decode context [extractHeader, vec4Type, output4, source3, 1] =
      .error (.inapplicable
        (.extract { resultType := vec4Type, result := output4, composite := source3, index := 1 })) := by
  rfl
example :
    decode context [construct4Header, vec4Type, output4, xId, yId, zId, 99] =
      .error (.inapplicable
        (.construct4
          { resultType := vec4Type, result := output4,
            x := xId, y := yId, z := zId, w := 99 })) := by
  rfl

-- Result IDs are fresh, and scalar/vector classifications and widths cannot conflict.
example :
    decode context [extractHeader, floatType, xId, source3, 0] =
      .error (.inapplicable
        (.extract { resultType := floatType, result := xId, composite := source3, index := 0 })) := by
  rfl

-- Type IDs share the SPIR-V ID namespace and cannot be reused as result IDs.
example :
    decode context [extractHeader, floatType, floatType, source3, 0] =
      .error (.inapplicable
        (.extract
          { resultType := floatType, result := floatType, composite := source3, index := 0 })) := by
  rfl

example :
    decode context [extractHeader, floatType, vec3Type, source3, 0] =
      .error (.inapplicable
        (.extract
          { resultType := floatType, result := vec3Type, composite := source3, index := 0 })) := by
  rfl

def contradictoryContext : Context :=
  { context with scalarType := fun id => id == floatType || id == vec3Type }

example : decode contradictoryContext extract1.encode =
    .error (.inapplicable extract1) := by rfl

def width5Context : Context :=
  { context with
    vectorType := fun id =>
      if id = vec3Type then some (floatType, 5) else context.vectorType id }

example : decode width5Context extract1.encode =
    .error (.inapplicable extract1) := by rfl

def before : Store Nat
  | id =>
      if id = source3 then some (.vector [10, 20, 30])
      else if id = xId then some (.scalar 1)
      else if id = yId then some (.scalar 2)
      else if id = zId then some (.scalar 3)
      else if id = wId then some (.scalar 4)
      else none

example : (transfer extract1 before).map (fun after => after extracted) =
    some (some (.scalar 20)) := by rfl
example : (transfer construct4 before).map (fun after => after output4) =
    some (some (.vector [1, 2, 3, 4])) := by rfl

example (suffix : List Word) :
    (decode context (extract1.encode ++ suffix)).map
      (fun result => (result.checked.val, result.rest)) = .ok (extract1, suffix) :=
  decode_encode_append context ⟨extract1, by decide⟩ suffix

end Tests.ISA.SPIRV.Composite
