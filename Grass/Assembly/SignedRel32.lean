/-!
# Checked signed 32-bit PC-relative displacements

This module performs only the arithmetic shared by branch and RIP-relative
encoders.  Offsets are natural byte positions, while the subtraction is done in
`Int`, so a backwards target is not truncated by natural-number subtraction.
-/

namespace Grass.Assembly.SignedRel32

private def lowerBound : Int := -(2 ^ 31)
private def upperBound : Int := 2 ^ 31

/-- The mathematical displacement from the end of an instruction to its target. -/
def displacement (sourceOffset instructionSize targetOffset : Nat) : Int :=
  (targetOffset : Int) - ((sourceOffset : Int) + (instructionSize : Int))

theorem displacement_translate (sourceOffset instructionSize targetOffset base : Nat) :
    displacement (sourceOffset + base) instructionSize (targetOffset + base) =
      displacement sourceOffset instructionSize targetOffset := by
  simp only [displacement, Int.natCast_add]
  omega

/-- A sealed successful conversion of one exact source/size/target triple. -/
structure Resolved where
  private mk ::
  sourceOffset : Nat
  instructionSize : Nat
  targetOffset : Nat
  bits : BitVec 32
  bitsExact : bits.toInt = displacement sourceOffset instructionSize targetOffset

/-- Resolve a PC-relative displacement, refusing values outside signed `i32`. -/
def resolve? (sourceOffset instructionSize targetOffset : Nat) : Option Resolved :=
  let delta := displacement sourceOffset instructionSize targetOffset
  if lower : lowerBound ≤ delta then
    if upper : delta < upperBound then
      some {
        sourceOffset := sourceOffset
        instructionSize := instructionSize
        targetOffset := targetOffset
        bits := BitVec.ofInt 32 delta
        bitsExact := by
          apply BitVec.toInt_ofInt_eq_self (by decide)
          · simpa [lowerBound] using lower
          · simpa [upperBound] using upper }
    else none
  else none

theorem resolve?_bits_translate (sourceOffset instructionSize targetOffset base : Nat) :
    (resolve? (sourceOffset + base) instructionSize (targetOffset + base)).map Resolved.bits =
      (resolve? sourceOffset instructionSize targetOffset).map Resolved.bits := by
  simp only [resolve?, displacement_translate]
  split <;> simp_all

/-- Successful resolution retains exactly the three inputs supplied to it. -/
theorem resolve?_inputs {sourceOffset instructionSize targetOffset : Nat}
    {resolved : Resolved}
    (success : resolve? sourceOffset instructionSize targetOffset = some resolved) :
    resolved.sourceOffset = sourceOffset ∧
      resolved.instructionSize = instructionSize ∧
      resolved.targetOffset = targetOffset := by
  dsimp only [resolve?] at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  simp only [Option.some.injEq] at success
  subst resolved
  exact ⟨rfl, rfl, rfl⟩

/-- The emitted bits recover the mathematical displacement without truncation. -/
theorem bits_no_truncation (resolved : Resolved) :
    resolved.bits.toInt =
      displacement resolved.sourceOffset resolved.instructionSize
        resolved.targetOffset :=
  resolved.bitsExact

/-- The resolved target is the next-instruction position plus the signed bits. -/
theorem target_equation (resolved : Resolved) :
    (resolved.targetOffset : Int) =
      (resolved.sourceOffset : Int) + (resolved.instructionSize : Int) +
        resolved.bits.toInt := by
  rw [bits_no_truncation resolved]
  simp only [displacement]
  omega

/-- A successful call exposes the target equation for the original inputs. -/
theorem target_equation_of_resolve? {sourceOffset instructionSize targetOffset : Nat}
    {resolved : Resolved}
    (success : resolve? sourceOffset instructionSize targetOffset = some resolved) :
    (targetOffset : Int) =
      (sourceOffset : Int) + (instructionSize : Int) + resolved.bits.toInt := by
  obtain ⟨hs, hi, ht⟩ := resolve?_inputs success
  rw [← hs, ← hi, ← ht]
  exact target_equation resolved

end Grass.Assembly.SignedRel32
