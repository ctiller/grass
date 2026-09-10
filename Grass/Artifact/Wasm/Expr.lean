import Grass.ISA.Wasm.Target.Encode

/-!
# A Wasm function body's expression

A Wasm function body is `locals* expr`, where `expr` is `instr* 0x0B`: a flat
instruction stream closed by one terminating `end` opcode.
`Grass.ISA.Wasm.Target.Function.body` (`Grass/ISA/Wasm/Target/Native.lean`)
does *not* carry that terminator itself — `State.step` treats "index past the
end of `body`" and "an `end_` with an empty label stack" identically
(`Grass/ISA/Wasm/Target/State.lean`), so the terminator is exactly the byte
this writer appends and this reader strips, never a member of `body`.

`decodeExpr` is written in the same "remainder" style as
`Grass.ISA.Wasm.Target.decodeAux` and this seam's other readers: it decodes
one instruction at a time and stops — returning `some []`, not consuming the
instruction it just decoded into the result — the moment doing so leaves no
bytes at all. Because every instruction's encoding is at least one byte
(`Grass.ISA.Wasm.Target.encode_pos`), that moment can only be the very last
byte of a closed byte range, which by construction is always the appended
`0x0B`; nesting (`block`/`loop`/`if_` opened by one instruction, closed by
their own `end_`) never triggers it, since a nested `end_` is always followed
by at least the outer terminator. This sidesteps needing this codec to track
block nesting at all — nesting is a run-time property of `State.step`, not a
byte-level framing property here.
-/
namespace Grass.Artifact.Wasm

open Grass.ISA.Wasm.Target (Instr encode decodeAux decodeAux_encode encode_pos)

/-- Canonical encoding of a flat instruction list, with no terminator. -/
def encodeInstrs (body : List Instr) : List UInt8 := (body.map encode).flatten

@[simp] theorem encodeInstrs_nil : encodeInstrs [] = [] := rfl

@[simp] theorem encodeInstrs_cons (instr : Instr) (body : List Instr) :
    encodeInstrs (instr :: body) = encode instr ++ encodeInstrs body := rfl

/-- No instruction encodes to nothing, so a list of `n` instructions encodes
to at least `n` bytes. This is exactly the fuel bound `decodeExpr` needs:
called with the *byte* length of a closed expression region (locals-vec
stripped, terminator included), there is always enough fuel to decode every
instruction in it. -/
theorem length_le_encodeInstrs (body : List Instr) : body.length ≤ (encodeInstrs body).length := by
  induction body with
  | nil => simp
  | cons instr body ih =>
      simp only [encodeInstrs_cons, List.length_append, List.length_cons]
      have := encode_pos instr
      omega

/-- The fuel bound `decodeExpr_encodeInstrs` needs, stated against the exact
byte length of the region `decodeExpr` is handed (the encoded body plus its
appended terminator), so a caller need not separately reconstruct it. -/
theorem length_lt_length_encodeInstrs_append (body : List Instr) :
    body.length < (encodeInstrs body ++ [0x0B]).length := by
  have := length_le_encodeInstrs body
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- Decode a function body's `expr` region from the head of `bytes`: every
instruction up to, but not including, the terminating `0x0B`. `fuel` bounds
recursion on the number of instructions left to decode (at most the number
of remaining bytes, since every instruction is at least one byte). -/
def decodeExpr : Nat → List UInt8 → Option (List Instr)
  | 0, _ => none
  | fuel + 1, bytes =>
      match decodeAux bytes with
      | none => none
      | some (instr, rest) =>
          if rest = [] then some []
          else
            match decodeExpr fuel rest with
            | none => none
            | some tail => some (instr :: tail)

/-- The expression round trip: decoding a body's own instructions plus the
appended terminator recovers exactly the instructions, with enough fuel
(strictly more than the instruction count, to also cover decoding the
terminator itself). -/
theorem decodeExpr_encodeInstrs (body : List Instr) (fuel : Nat) (enough : body.length < fuel) :
    decodeExpr fuel (encodeInstrs body ++ [0x0B]) = some body := by
  induction body generalizing fuel with
  | nil =>
      obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      show decodeExpr (fuel + 1) [0x0B] = some []
      have step : decodeAux ([0x0B] ++ ([] : List UInt8)) = some (Instr.end_, []) :=
        decodeAux_encode Instr.end_ []
      simp only [List.append_nil] at step
      unfold decodeExpr
      rw [step]
      simp
  | cons instr body ih =>
      obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
      have shape : encodeInstrs (instr :: body) ++ [0x0B] =
          encode instr ++ (encodeInstrs body ++ [0x0B]) := by
        simp [encodeInstrs, List.append_assoc]
      have step : decodeAux (encode instr ++ (encodeInstrs body ++ [0x0B])) =
          some (instr, encodeInstrs body ++ [0x0B]) := decodeAux_encode instr _
      have nonempty : encodeInstrs body ++ [0x0B] ≠ [] := by simp
      have restEnough : body.length < fuel := by
        rw [List.length_cons] at enough
        omega
      rw [shape]
      unfold decodeExpr
      rw [step]
      simp only [nonempty, if_neg, not_false_iff]
      rw [ih fuel restEnough]

end Grass.Artifact.Wasm
