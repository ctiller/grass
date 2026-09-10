import Grass.Target.ISA
import Grass.Assembly.Syntax.AST

/-!
# The lowering seam

One ISA's answer to "what does this authored line become". `size` is what
pass 1 sums to place labels and may read only address-independent facts
(`Env`); `lower` is what pass 2 emits once every label address is known.
`lower_size` binds the two, so an ISA with several encodable widths for the
same line must pick one canonically inside its own instance.

Nothing here names a mnemonic, a register, or a program: those live in the
per-ISA instance, and the layout theorems (`Grass/Assembly/Lower/Layout.lean`)
are proved once against this record.
-/

namespace Grass.Assembly.Lower

open Grass.Assembly.Syntax

/-- The first binding of `name`. Appending never shadows: a table built by
`left ++ right` answers from `left` wherever `left` answers at all. -/
def lookup : List (String × Nat) → String → Option Nat
  | [], _ => none
  | (key, value) :: rest, name => if key = name then some value else lookup rest name

theorem lookup_append_left {left : List (String × Nat)} {name : String} {value : Nat}
    (found : lookup left name = some value) (right : List (String × Nat)) :
    lookup (left ++ right) name = some value := by
  induction left with
  | nil => simp [lookup] at found
  | cons head tail ih =>
      obtain ⟨key, entry⟩ := head
      by_cases same : key = name
      · rw [lookup, if_pos same] at found
        rw [List.cons_append, lookup, if_pos same]
        exact found
      · rw [lookup, if_neg same] at found
        rw [List.cons_append, lookup, if_neg same]
        exact ih found

theorem lookup_append_fresh {left : List (String × Nat)} {name : String}
    (absent : lookup left name = none) (value : Nat) :
    lookup (left ++ [(name, value)]) name = some value := by
  induction left with
  | nil => simp [lookup]
  | cons head tail ih =>
      obtain ⟨key, entry⟩ := head
      by_cases same : key = name
      · rw [lookup, if_pos same] at absent
        exact absurd absent (by simp)
      · rw [lookup, if_neg same] at absent
        rw [List.cons_append, lookup, if_neg same]
        exact ih absent

/-- The address-independent facts a lowering may read. There is deliberately
no label address here: a size computed from an `Env` cannot depend on where
its line lands, which is what makes the two-pass layout sound. -/
structure Env where
  /-- A named constant: an imported, static, or platform value. -/
  constant : String → Option Int
  /-- The byte size `sizeof(name)` denotes. -/
  sizeOf : String → Option Nat
  /-- The byte offset of a declared frame local from the frame base. -/
  slot : String → Option Nat
  /-- Bytes the frame occupies. -/
  frameBytes : Nat

/-- Frame slots for `locals`, `slotBytes` apart, in declaration order. -/
def slotTable (slotBytes : Nat) : Nat → List Local → List (String × Nat)
  | _, [] => []
  | offset, item :: rest => (item.name, offset) :: slotTable slotBytes (offset + slotBytes) rest

/-- The environment of a source whose locals each occupy `slotBytes`. -/
def Env.ofLocals (slotBytes : Nat) (locals : List Local)
    (constant : String → Option Int) (sizeOf : String → Option Nat) : Env where
  constant := constant
  sizeOf := sizeOf
  slot := lookup (slotTable slotBytes 0 locals)
  frameBytes := slotBytes * locals.length

/-- What one ISA contributes to the assembler. -/
structure Lowering (isa : Grass.Target.ISA) where
  /-- The byte length the line will occupy, from address-independent facts
  alone. -/
  size : Line → Env → Except String Nat
  /-- The instructions the line becomes, given every label address and the
  address of the line itself. -/
  lower : Line → Env → (labels : String → Option Nat) → (pc : Nat) →
    Except String (List isa.Instr)
  /-- Whatever `lower` emits occupies exactly the bytes `size` promised. An
  ISA with a variable-length form must therefore commit to one width in its
  own instance; it cannot shrink a branch after pass 1. -/
  lower_size : ∀ (line : Line) (env : Env) (labels : String → Option Nat) (pc : Nat)
      (instrs : List isa.Instr),
    lower line env labels pc = .ok instrs →
    size line env = .ok (isa.encodeAll instrs).length

namespace Lowering

variable {isa : Grass.Target.ISA}

/-- The total size of a run of lines. -/
def sizes (low : Lowering isa) (env : Env) : List Line → Except String Nat
  | [] => .ok 0
  | line :: rest =>
    match low.size line env with
    | .error message => .error message
    | .ok here =>
      match low.sizes env rest with
      | .error message => .error message
      | .ok later => .ok (here + later)

/-- Sizing a run of lines sizes each of its parts. This is what turns a
whole-source pass into the `sizes env before = .ok span` the layout theorems
ask for. -/
theorem sizes_append (low : Lowering isa) (env : Env) :
    ∀ (before rest : List Line) (total : Nat),
      low.sizes env (before ++ rest) = .ok total →
      ∃ span later, low.sizes env before = .ok span ∧ low.sizes env rest = .ok later ∧
        total = span + later := by
  intro before
  induction before with
  | nil =>
      intro rest total summed
      rw [List.nil_append] at summed
      exact ⟨0, total, by rw [sizes], summed, by omega⟩
  | cons line before ih =>
      intro rest total summed
      rw [List.cons_append, sizes] at summed
      split at summed
      · simp at summed
      · rename_i width sized
        split at summed
        · simp at summed
        · rename_i restSpan restSummed
          obtain ⟨span, later, headSummed, tailSummed, total_eq⟩ := ih rest restSpan restSummed
          cases summed
          refine ⟨width + span, later, ?_, tailSummed, by omega⟩
          rw [sizes, sized, headSummed]

/-- Pass 2 over a run of lines starting at `pc`. -/
def emit (low : Lowering isa) (env : Env) (labels : String → Option Nat) :
    List Line → Nat → Except String (List isa.Instr)
  | [], _ => .ok []
  | line :: rest, pc =>
    match low.lower line env labels pc with
    | .error message => .error message
    | .ok here =>
      match low.size line env with
      | .error message => .error message
      | .ok width =>
        match low.emit env labels rest (pc + width) with
        | .error message => .error message
        | .ok later => .ok (here ++ later)

/-- Pass 2 emits exactly the bytes pass 1 counted. -/
theorem emit_length (low : Lowering isa) (env : Env) (labels : String → Option Nat) :
    ∀ (lines : List Line) (pc : Nat) (out : List isa.Instr) (total : Nat),
      low.emit env labels lines pc = .ok out → low.sizes env lines = .ok total →
      (isa.encodeAll out).length = total := by
  intro lines
  induction lines with
  | nil =>
      intro pc out total emitted summed
      rw [emit] at emitted
      rw [sizes] at summed
      cases emitted
      cases summed
      simp
  | cons line rest ih =>
      intro pc out total emitted summed
      rw [emit] at emitted
      rw [sizes] at summed
      split at emitted
      · simp at emitted
      · rename_i here lowered
        split at emitted
        · simp at emitted
        · rename_i width sized
          split at emitted
          · simp at emitted
          · rename_i later tailEmitted
            simp only [sized] at summed
            split at summed
            · simp at summed
            · rename_i tail tailSummed
              have headBytes : low.size line env = .ok (isa.encodeAll here).length :=
                low.lower_size line env labels pc here lowered
              rw [sized] at headBytes
              have headEq : width = (isa.encodeAll here).length := by
                exact Except.ok.inj headBytes
              have tailEq : (isa.encodeAll later).length = tail := ih _ _ _ tailEmitted tailSummed
              cases emitted
              cases summed
              rw [Grass.Target.ISA.encodeAll_append, List.length_append, tailEq, headEq]

/-- Pass 2 over `before ++ rest` is pass 2 over `before` followed by pass 2
over `rest`, started at the address `before`'s sizes reach. -/
theorem emit_append (low : Lowering isa) (env : Env) (labels : String → Option Nat) :
    ∀ (before rest : List Line) (pc : Nat) (out : List isa.Instr) (span : Nat),
      low.emit env labels (before ++ rest) pc = .ok out →
      low.sizes env before = .ok span →
      ∃ head tail, out = head ++ tail ∧
        low.emit env labels before pc = .ok head ∧
        (isa.encodeAll head).length = span ∧
        low.emit env labels rest (pc + span) = .ok tail := by
  intro before
  induction before with
  | nil =>
      intro rest pc out span emitted summed
      rw [sizes] at summed
      cases summed
      refine ⟨[], out, by simp, by rw [emit], by simp, ?_⟩
      simpa using emitted
  | cons line before ih =>
      intro rest pc out span emitted summed
      rw [List.cons_append, emit] at emitted
      rw [sizes] at summed
      split at emitted
      · simp at emitted
      · rename_i here lowered
        split at emitted
        · simp at emitted
        · rename_i width sized
          split at emitted
          · simp at emitted
          · rename_i later tailEmitted
            simp only [sized] at summed
            split at summed
            · simp at summed
            · rename_i tailSpan tailSummed
              obtain ⟨head, tail, splitOut, headEmitted, headBytes, tailRest⟩ :=
                ih rest (pc + width) later tailSpan tailEmitted tailSummed
              have headWidth : low.size line env = .ok (isa.encodeAll here).length :=
                low.lower_size line env labels pc here lowered
              rw [sized] at headWidth
              have widthEq : width = (isa.encodeAll here).length := Except.ok.inj headWidth
              cases emitted
              cases summed
              refine ⟨here ++ head, tail, by rw [splitOut, List.append_assoc], ?_, ?_, ?_⟩
              · simp only [emit, lowered, sized, headEmitted]
              · rw [Grass.Target.ISA.encodeAll_append, List.length_append, headBytes, widthEq]
              · rw [← Nat.add_assoc]
                exact tailRest

end Lowering

end Grass.Assembly.Lower
