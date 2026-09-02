/-!
# Finite multisets of abstract demands

`docs/PROCESS.md` §2 gives `ProcessSpec.Step` an `AbstractDemandBag Demand`
output and says what that container must and must not be:

> The finite demand multiset contains neither occurrence identities nor
> execution order.

and

> Equal demand values remain indistinguishable at the precious level, but their
> bag multiplicity cannot be fabricated, replayed, jointly consumed by one
> result, or silently lost.

Those two sentences pick the representation. Order must be quotiented away, or
a specification would observe the order in which a transition happened to list
its demands — a schedule fact, forbidden by `docs/FOUNDATION.md` law 18.
Multiplicity must *not* be quotiented away, or two identical outstanding
`WriteFile` demands would be one, and one completion would discharge both. A
`List` quotiented by permutation is exactly the container with the first
property and not the second; a `Set` or a `List` alone has one property and not
the other.

## Consumption is definitional, not a side condition

`ConsumeExactlyOneMatching outstanding demand remainder` is *defined* as
`outstanding = remainder.cons demand`. This is the whole content of "consumes
exactly one live matching item". It is not an extra invariant checked alongside
the transition: a `ProcessRunTransition.stepResult` cannot be formed at all
without exhibiting the remainder, and `cons_injective_right` then says that
remainder is unique. No proof obligation can be discharged by weakening it to
membership, because membership is not what the constructor asks for.

## Custody note

`Grass.Process` is not the owner of general collection types.
`docs/MODULES.md` gives pure collections and their algebraic laws to
`Grass.Std.Logical`, and `docs/PROCESS_IMPLEMENTATION_PLAN.md` §2.2 records this
module as temporary custody: no multiset exists in Lean core or on any branch,
and `ProcessSpec` cannot be stated without one.

The handover is designed to be a rename and a re-export. This module carries
only the operations and laws the process layer consumes, and it carries no
process vocabulary — nothing here mentions a demand, an occurrence, or a
transition. The process-specific reading of these laws (that they are what
forbids fabrication, duplication, joint consumption, and loss) lives at the use
sites in `Grass/Process/Run.lean`, not here.
-/

namespace Grass.Process

universe u v

/--
A finite multiset over `α`: a list up to permutation.

`Quotient (List.isSetoid α)` is `List α` quotiented by `List.Perm`. Working
through `Quotient.mk` rather than an inductive type means every law below is
inherited from an existing `List.Perm` lemma instead of being re-proved.
-/
def Bag (α : Type u) : Type u := Quotient (List.isSetoid α)

namespace Bag

variable {α : Type u} {β : Type v}

/-- The multiset containing exactly the elements of `elements`, in any order. -/
def ofList (elements : List α) : Bag α := Quotient.mk (List.isSetoid α) elements

instance : Coe (List α) (Bag α) := ⟨ofList⟩

/-- The empty multiset. Written `0`; it is the unit of `+`. -/
protected def empty : Bag α := ofList []

instance : EmptyCollection (Bag α) := ⟨Bag.empty⟩
instance : Zero (Bag α) := ⟨Bag.empty⟩

/-- The multiset containing `element` once. -/
def singleton (element : α) : Bag α := ofList [element]

instance : Singleton α (Bag α) := ⟨singleton⟩

/-- Add one occurrence of `element`. Multiplicity increases by exactly one. -/
def cons (element : α) (rest : Bag α) : Bag α :=
  Quotient.liftOn rest (fun elements => ofList (element :: elements))
    (fun _ _ equivalent => Quotient.sound (equivalent.cons element))

/-- Multiset union: multiplicities add. Written `+`. -/
protected def append (left right : Bag α) : Bag α :=
  Quotient.liftOn₂ left right (fun l r => ofList (l ++ r))
    (fun _ _ _ _ leftEquivalent rightEquivalent =>
      Quotient.sound (leftEquivalent.append rightEquivalent))

instance : Add (Bag α) := ⟨Bag.append⟩
instance : Append (Bag α) := ⟨Bag.append⟩

/--
Membership. `element ∈ bag` says the multiplicity of `element` is at least one;
it deliberately says nothing about how many.
-/
protected def Mem (bag : Bag α) (element : α) : Prop :=
  Quotient.liftOn bag (fun elements => element ∈ elements)
    (fun _ _ equivalent => propext equivalent.mem_iff)

instance : Membership α (Bag α) := ⟨Bag.Mem⟩

/-- The number of occurrences in the multiset, counting multiplicity. -/
def card (bag : Bag α) : Nat :=
  Quotient.liftOn bag List.length (fun _ _ equivalent => equivalent.length_eq)

/-- Image under `f`. Multiplicity is preserved, so this is not a set image. -/
def map (f : α → β) (bag : Bag α) : Bag β :=
  Quotient.liftOn bag (fun elements => ofList (elements.map f))
    (fun _ _ equivalent => Quotient.sound (equivalent.map f))

section Reduction

/-!
Every operation above is a `Quotient.liftOn` of a list operation, so each
reduces definitionally on a representative. These six lemmas are the only place
that fact is used; everything below goes through `Quotient.inductionOn` and then
`simp` with these.
-/

@[simp] theorem ofList_nil : ofList ([] : List α) = 0 := rfl

@[simp] theorem ofList_cons (element : α) (elements : List α) :
    ofList (element :: elements) = cons element (ofList elements) := rfl

@[simp] theorem ofList_append (left right : List α) :
    ofList (left ++ right) = ofList left + ofList right := rfl

@[simp] theorem card_ofList (elements : List α) :
    card (ofList elements) = elements.length := rfl

@[simp] theorem mem_ofList {element : α} {elements : List α} :
    element ∈ ofList elements ↔ element ∈ elements := Iff.rfl

@[simp] theorem singleton_eq (element : α) :
    ({element} : Bag α) = ofList [element] := rfl

end Reduction

section Algebra

@[simp] theorem zero_add (bag : Bag α) : 0 + bag = bag := by
  induction bag using Quotient.inductionOn with
  | _ elements => rfl

@[simp] theorem add_zero (bag : Bag α) : bag + 0 = bag := by
  induction bag using Quotient.inductionOn with
  | _ elements => exact congrArg ofList (List.append_nil elements)

theorem add_assoc (a b c : Bag α) : a + b + c = a + (b + c) := by
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      induction c using Quotient.inductionOn with
      | _ z => exact congrArg ofList (List.append_assoc x y z)

theorem add_comm (a b : Bag α) : a + b = b + a := by
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y => exact Quotient.sound List.perm_append_comm

@[simp] theorem card_zero : card (0 : Bag α) = 0 := rfl

@[simp] theorem card_cons (element : α) (rest : Bag α) :
    card (cons element rest) = card rest + 1 := by
  induction rest using Quotient.inductionOn with
  | _ elements => rfl

@[simp] theorem card_add (a b : Bag α) : card (a + b) = card a + card b := by
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y => exact List.length_append

@[simp] theorem mem_zero (element : α) : ¬ (element ∈ (0 : Bag α)) :=
  List.not_mem_nil

@[simp] theorem mem_cons {element head : α} {rest : Bag α} :
    element ∈ cons head rest ↔ element = head ∨ element ∈ rest := by
  induction rest using Quotient.inductionOn with
  | _ elements => exact List.mem_cons

@[simp] theorem mem_singleton {element head : α} :
    element ∈ ({head} : Bag α) ↔ element = head :=
  List.mem_singleton

@[simp] theorem mem_add {element : α} {a b : Bag α} :
    element ∈ a + b ↔ element ∈ a ∨ element ∈ b := by
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y => exact List.mem_append

/--
`cons` is `+ {element}`. Both spellings appear in `docs/PROCESS.md`: the run
transitions add issued bags with `+`, while a single demand is naturally consed.
-/
theorem cons_eq_singleton_add (element : α) (rest : Bag α) :
    cons element rest = {element} + rest := by
  induction rest using Quotient.inductionOn with
  | _ elements => rfl

theorem add_cons (element : α) (a b : Bag α) :
    a + cons element b = cons element (a + b) := by
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      exact Quotient.sound (List.perm_middle (a := element) (l₁ := x) (l₂ := y))

end Algebra

section Consumption

/--
`cons` is injective in its second argument: if adding one occurrence of the same
element to two multisets yields the same multiset, the multisets were equal.

This is what makes the remainder in `ConsumeExactlyOneMatching` unique, and so
what makes "consumes exactly one" a determinate claim rather than a choice among
several possible remainders.
-/
theorem cons_injective_right {element : α} {left right : Bag α}
    (equal : cons element left = cons element right) : left = right := by
  induction left using Quotient.inductionOn with
  | _ x =>
    induction right using Quotient.inductionOn with
    | _ y =>
      exact Quotient.sound
        ((List.perm_cons element).mp (Quotient.exact equal))

/--
A consumption witness: `outstanding` is `remainder` plus exactly one occurrence
of `element`.

`docs/PROCESS.md` §2 requires that a result or interruption "requires and
consumes exactly one live matching item". Stating that as an equation rather
than as a side condition on a membership proof is what forbids the four failure
modes the document names. Fabrication is impossible because `outstanding` must
already contain the occurrence. Duplication is impossible because exactly one
`cons` is removed. Joint consumption is impossible because one equation removes
one occurrence, whatever the multiplicity of equal values. Loss is impossible
because `remainder` is the whole rest of the bag, not an arbitrary sub-bag.
-/
def ConsumeExactlyOneMatching (outstanding : Bag α) (element : α)
    (remainder : Bag α) : Prop :=
  outstanding = cons element remainder

theorem ConsumeExactlyOneMatching.mem
    {outstanding : Bag α} {element : α} {remainder : Bag α}
    (consume : ConsumeExactlyOneMatching outstanding element remainder) :
    element ∈ outstanding := by
  subst consume; simp

theorem ConsumeExactlyOneMatching.card
    {outstanding : Bag α} {element : α} {remainder : Bag α}
    (consume : ConsumeExactlyOneMatching outstanding element remainder) :
    outstanding.card = remainder.card + 1 := by
  subst consume; simp

/-- The remainder of a consumption is unique. -/
theorem ConsumeExactlyOneMatching.remainder_unique
    {outstanding : Bag α} {element : α} {left right : Bag α}
    (first : ConsumeExactlyOneMatching outstanding element left)
    (second : ConsumeExactlyOneMatching outstanding element right) :
    left = right :=
  cons_injective_right (first ▸ second : cons element left = cons element right)

/-- Nothing can be consumed from an empty outstanding set. -/
theorem not_consume_zero {element : α} {remainder : Bag α} :
    ¬ ConsumeExactlyOneMatching 0 element remainder := by
  intro consume
  exact absurd (consume.card) (by simp)

/--
An element can be consumed exactly when it is present. The forward direction is
`ConsumeExactlyOneMatching.mem`; the reverse is what lets a specification say
"there is an outstanding `d`" and obtain the transition.
-/
theorem consume_iff_mem [BEq α] [LawfulBEq α] {outstanding : Bag α} {element : α} :
    (∃ remainder, ConsumeExactlyOneMatching outstanding element remainder) ↔
      element ∈ outstanding := by
  constructor
  · rintro ⟨remainder, consume⟩; exact consume.mem
  · induction outstanding using Quotient.inductionOn with
    | _ elements =>
      intro member
      exact ⟨ofList (elements.erase element),
        Quotient.sound (List.perm_cons_erase member)⟩

end Consumption

end Bag

end Grass.Process
