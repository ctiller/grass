/-!
Bounded WGSL vector-composite expressions.

This is a shader-language fragment, not a machine ISA.  It covers the source
form `vec4<f32>(a[i], b[j], c[k], d[l])`, where each named operand is a
`vec2<f32>`, `vec3<f32>`, or `vec4<f32>` and every selected lane is in range.
The model is polymorphic in the semantic scalar `α`: it proves only selection
and reassembly of lanes, and makes no claim about f32 representations or
floating-point evaluation.

The source rule follows the W3C WGSL Candidate Recommendation Draft, 31 August
2026, sections [6.2.6 Vector Types](https://www.w3.org/TR/2026/CRD-WGSL-20260831/#vector-types),
[6.2.12 Constructible Types](https://www.w3.org/TR/2026/CRD-WGSL-20260831/#constructible-types),
[8.5.1 Vector Access Expression](https://www.w3.org/TR/2026/CRD-WGSL-20260831/#vector-access-expression),
and [`vec4` constructors](https://www.w3.org/TR/2026/CRD-WGSL-20260831/#vec4-builtin).
This parser operates at token boundaries and admits only generated variable
identifiers `v0`, `v1`, and so on; it deliberately does not
implement WGSL's full text grammar, modules,
uniformity analysis, or provider/pipeline validation.

The surrounding scope checker must establish that `vec4` and `f32` resolve to
the WGSL builtins at this expression site.  This fragment performs no implicit
module-level name-resolution or global validation.
-/

namespace Grass.Shader.WGSL.Composite

/-- The explicit scalar tags accepted by this bounded checker. -/
inductive ScalarType where
  | f32 | i32 | u32
  deriving DecidableEq, Repr

/-- The sole result type of this primitive family. -/
structure Vec4 (α : Type) where
  x : α
  y : α
  z : α
  w : α
  deriving Repr

/-- A named operand supplied by the surrounding shader checker. -/
structure Operand (α : Type) where
  scalar : ScalarType
  width : Nat
  lanes : Fin width → α

/-- A generated WGSL identifier.  Rendering this as `v` followed by its index
is a syntactically valid, non-reserved identifier subset. -/
structure Identifier where
  index : Nat
  deriving DecidableEq, Repr

def Identifier.render (identifier : Identifier) : String :=
  "v" ++ toString identifier.index

/-- The source-level selector for one vector component. -/
structure LaneRef where
  name : Identifier
  lane : Nat
  deriving DecidableEq, Repr

/-- The narrow accepted AST: four component expressions in a `vec4<f32>` constructor. -/
structure Source where
  first : LaneRef
  second : LaneRef
  third : LaneRef
  fourth : LaneRef
  deriving DecidableEq, Repr

/-- A small WGSL token grammar used by the writer and checked parser.

`uintLiteral` represents the `u`-suffixed index token.  This fragment only
accepts indices below four, so every accepted index is representable by WGSL
`u32`; it does not claim to validate arbitrary numeric literal spellings.
-/
inductive Token where
  | vec4 | f32 | i32 | u32 | lt | gt | lparen | rparen | lbracket | rbracket | comma
  | ident (name : Identifier) | uintLiteral (index : Nat)
  deriving DecidableEq, Repr

def Token.render : Token → String
  | .vec4 => "vec4"
  | .f32 => "f32"
  | .i32 => "i32"
  | .u32 => "u32"
  | .lt => "<"
  | .gt => ">"
  | .lparen => "("
  | .rparen => ")"
  | .lbracket => "["
  | .rbracket => "]"
  | .comma => ","
  | .ident identifier => identifier.render
  | .uintLiteral index => toString index ++ "u"

def Token.renderMany (tokens : List Token) : String :=
  tokens.foldl (fun text token => text ++ token.render) ""

def write (source : Source) : List Token :=
  [.vec4, .lt, .f32, .gt, .lparen,
   .ident source.first.name, .lbracket, .uintLiteral source.first.lane, .rbracket, .comma,
   .ident source.second.name, .lbracket, .uintLiteral source.second.lane, .rbracket, .comma,
   .ident source.third.name, .lbracket, .uintLiteral source.third.lane, .rbracket, .comma,
   .ident source.fourth.name, .lbracket, .uintLiteral source.fourth.lane, .rbracket, .rparen]

/-- Canonical WGSL expression text for this fragment.  Only the token
round-trip below is proved; a general WGSL text lexer is intentionally outside
this bounded primitive. -/
def writeText (source : Source) : String := Token.renderMany (write source)

private def parseRef? : List Token → Option (LaneRef × List Token)
  | .ident name :: .lbracket :: .uintLiteral lane :: .rbracket :: rest => some ({ name, lane }, rest)
  | _ => none

/-- Parse precisely this token-bounded constructor grammar. -/
def parse? : List Token → Option Source
  | .vec4 :: .lt :: .f32 :: .gt :: .lparen :: tokens => do
    let (first, tokens) ← parseRef? tokens
    let .comma :: tokens := tokens | none
    let (second, tokens) ← parseRef? tokens
    let .comma :: tokens := tokens | none
    let (third, tokens) ← parseRef? tokens
    let .comma :: tokens := tokens | none
    let (fourth, tokens) ← parseRef? tokens
    let [.rparen] := tokens | none
    some { first, second, third, fourth }
  | _ => none

theorem parse_write (source : Source) : parse? (write source) = some source := by
  cases source
  simp [write, parse?, parseRef?]

/-- A supplied operand is eligible only as a typed `vecN<f32>` for N = 2, 3, or 4. -/
def eligible {α : Type} (operand : Operand α) : Bool :=
  operand.scalar == .f32 && (operand.width == 2 || operand.width == 3 || operand.width == 4)

/-- Check one source selector against the surrounding typed operand environment. -/
def select? {α : Type} (environment : Identifier → Option (Operand α)) (reference : LaneRef) : Option α := do
  let operand ← environment reference.name
  guard (eligible operand)
  if h : reference.lane < operand.width then
    some (operand.lanes ⟨reference.lane, h⟩)
  else
    none

/-- Decode the accepted source AST directly into its lane-preserving semantic operation. -/
def decode? {α : Type} (environment : Identifier → Option (Operand α)) (source : Source) : Option (Vec4 α) := do
  let x ← select? environment source.first
  let y ← select? environment source.second
  let z ← select? environment source.third
  let w ← select? environment source.fourth
  some { x, y, z, w }

/-- Checked source entry point: parsing and typed semantic decoding are one operation. -/
def check? {α : Type} (environment : Identifier → Option (Operand α)) (tokens : List Token) : Option (Vec4 α) := do
  let source ← parse? tokens
  decode? environment source

theorem check_write {α : Type} (environment : Identifier → Option (Operand α)) (source : Source) :
    check? environment (write source) = decode? environment source := by
  simp [check?, parse_write]

/-- Any accepted token sequence has an AST whose typed decoding is exactly the checked result. -/
theorem check_sound {α : Type} (environment : Identifier → Option (Operand α))
    (tokens : List Token) (result : Vec4 α)
    (accepted : check? environment tokens = some result) :
    ∃ source, parse? tokens = some source ∧ decode? environment source = some result := by
  cases parsed : parse? tokens with
  | none => simp [check?, parsed] at accepted
  | some source =>
    exact ⟨source, rfl, by simpa [check?, parsed] using accepted⟩

/-- `Grass.Shader.WGSL.Composite.decode_lanes` identifies the semantic result's
four lanes with the four successful operand selections. -/
theorem decode_lanes {α : Type} (environment : Identifier → Option (Operand α)) (source : Source)
    (x y z w : α)
    (hx : select? environment source.first = some x)
    (hy : select? environment source.second = some y)
    (hz : select? environment source.third = some z)
    (hw : select? environment source.fourth = some w) :
    decode? environment source = some { x, y, z, w } := by
  simp [decode?, hx, hy, hz, hw]

end Grass.Shader.WGSL.Composite
