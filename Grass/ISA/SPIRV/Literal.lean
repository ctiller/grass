/-!
Checked finite literal encodings for the bounded SPIR-V source reader.
OpConstant uses the scalar type's bit representation (Khronos SPIR-V,
https://registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html#OpConstant).
Binary32 field interpretation follows the IEEE single-format table in Oracle's
Numerical Computation Guide, https://docs.oracle.com/cd/E19957-01/806-3568/ncg_math.html.
Only exactly representable decimal inputs are accepted; no rounding or runtime
floating-point arithmetic is used. Candidate construction is checked against
the independently defined sign/exponent/fraction rational interpretation.
-/
namespace Grass.ISA.SPIRV.Literal

abbrev Word := BitVec 32

def decimalNat? (text : String) : Option Nat :=
  if text.isEmpty then none else
    text.toList.foldlM (fun n c =>
      if '0' ≤ c && c ≤ '9' then some (10 * n + (c.toNat - '0'.toNat)) else none) 0

def parseWord32? (text : String) : Option Word := do
  let n ← decimalNat? text
  if n < 2^32 then some (BitVec.ofNat 32 n) else none

def int32? (signed : Bool) (text : String) : Option Word := do
  let chars := text.toList
  if chars.head? = some '-' then
    let n ← decimalNat? (String.ofList chars.tail)
    if signed && n ≤ 2^31 then some (BitVec.ofNat 32 (2^32 - n)) else none
  else
    let n ← decimalNat? text
    if n < (if signed then 2^31 else 2^32) then some (BitVec.ofNat 32 n) else none

structure Decimal where
  negative : Bool
  numerator : Nat
  scale : Nat
  deriving DecidableEq, Repr

def Decimal.denominator (value : Decimal) : Nat := 10^value.scale

def decimal? (text : String) : Option Decimal := do
  let chars := text.toList
  let negative := chars.head? = some '-'
  let magnitude := if negative then chars.tail else chars
  let whole := magnitude.takeWhile (· != '.')
  match magnitude.drop whole.length with
  | [] =>
      let numerator ← decimalNat? (String.ofList whole)
      some ⟨negative, numerator, 0⟩
  | '.' :: fractional =>
      let integral ← decimalNat? (String.ofList whole)
      let fractionalValue ← decimalNat? (String.ofList fractional)
      some ⟨negative, integral * 10^fractional.length + fractionalValue, fractional.length⟩
  | _ => none

/-- Exact finite magnitude as numerator/denominator, including subnormals. -/
def magnitude? (word : Word) : Option (Nat × Nat) :=
  let exponent := (word.toNat / 2^23) % 256
  let fraction := word.toNat % 2^23
  if exponent = 255 then none
  else if exponent = 0 then some (fraction, 2^149)
  else if exponent ≤ 150 then some (2^23 + fraction, 2^(150 - exponent))
  else some ((2^23 + fraction) * 2^(exponent - 150), 1)

def Decimal.EncodedBy (value : Decimal) (word : Word) : Prop :=
  (decide (2^31 ≤ word.toNat) = value.negative) ∧
  match magnitude? word with
  | none => False
  | some (n, d) => n * value.denominator = value.numerator * d

instance (value : Decimal) (word : Word) : Decidable (value.EncodedBy word) := by
  unfold Decimal.EncodedBy
  cases h : magnitude? word with
  | none => infer_instance
  | some pair => cases pair; infer_instance

/-- An efficient candidate; acceptance is governed by `EncodedBy`, not this algorithm. -/
def candidate? (value : Decimal) : Option Word := do
  if value.numerator = 0 then
    some (BitVec.ofNat 32 (if value.negative then 2^31 else 0))
  else
    let denominator := value.denominator
    let e : Int := Int.ofNat value.numerator.log2 - Int.ofNat denominator.log2
    let below := if 0 ≤ e then value.numerator < denominator * 2^e.toNat
      else value.numerator * 2^(-e).toNat < denominator
    let unbiased := if below then e - 1 else e
    let field := if unbiased < -126 then 0 else (unbiased + 127).toNat
    if 255 ≤ field then none else
      let scaled := if field = 0 then value.numerator * 2^149 / denominator
        else if field ≤ 150 then value.numerator * 2^(150-field) / denominator
        else value.numerator / (denominator * 2^(field-150))
      let fraction := if field = 0 then scaled else scaled - 2^23
      some (BitVec.ofNat 32 ((if value.negative then 2^31 else 0) + field * 2^23 + fraction))

def float32Exact? (text : String) : Option Word := do
  let value ← decimal? text
  let candidate ← candidate? value
  if value.EncodedBy candidate then some candidate else none

/-- Successful encoding proves exact rational/sign agreement for the parsed input. -/
theorem float32Exact?_sound (text : String) (word : Word)
    (accepted : float32Exact? text = some word) :
    ∃ value, decimal? text = some value ∧ value.EncodedBy word := by
  cases parsed : decimal? text with
  | none => simp [float32Exact?, parsed] at accepted
  | some value =>
      cases candidate : candidate? value with
      | none => simp [float32Exact?, parsed, candidate] at accepted
      | some bits =>
          by_cases exactBits : value.EncodedBy bits
          · simp [float32Exact?, parsed, candidate, exactBits] at accepted
            subst word
            exact ⟨value, rfl, exactBits⟩
          · simp [float32Exact?, parsed, candidate, exactBits] at accepted

end Grass.ISA.SPIRV.Literal
