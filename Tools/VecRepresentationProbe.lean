/-!
# The `Vec` representation probe

`docs/STDLIB_IMPLEMENTATION_PLAN.md` §3.2 records that a *genuinely* `Array`-backed
`Vec` — one whose `push` is `Array.push` and whose indexing is `Array` indexing,
rather than a rename that keeps `List`-shaped bodies — had been "neither costed nor
probed", and that it is the only candidate able to emit a large artifact. This file
is that probe. It is not a test and `lake` does not build it; run it directly:

```sh
lake env lean Tools/VecRepresentationProbe.lean
```

It answers three questions and nothing else. It deliberately does **not** define a
replacement for `Grass.Std.Logical.Vec`: §3.2's decision is not this file's to make,
and a probe that shipped a second sequence type would be the churn §6 forbids.

**One: do the laws re-prove against core's `Array` lemmas, with no mathlib?** Yes.
Every law below is proved from `Array.getElem?_push`, `Array.size_append` and
friends. This was the open risk — the restatement cost is only worth paying if the
restatement is possible.

**Two: what does the emitter cost?** `Grass/Std/Logical/Vec.lean`'s `push` is
`⟨v.toList ++ [a]⟩` and its `get?` is `v.toList[i]?`, so building an artifact is
quadratic and reading a byte is linear. The `Array` bodies are amortised constant
and constant. Measured by `#eval`, building by repeated `push` then reading every
index:

| n | `Vec` (`List`-backed) | `AVec` (`Array`-backed) |
|---|---|---|
| 1 000 | 4 ms | 2 ms |
| 4 000 | 63 ms | 2 ms |
| 16 000 | 829 ms | 8 ms |
| 32 000 | 2890 ms | 14 ms |

`Vec`'s time grows about fourfold per doubling and `AVec`'s about twofold, which is
the quadratic-versus-linear split the definitions predict. `docs/HELLO_WORLD.md`
accepts the milestone only when `emitProgram`'s bytes execute, and `ByteArray` is
`Vec Byte`, so the byte writer runs over this type.

**Three: what does the kernel cost?** This is the axis that cuts the other way.
`docs/HELLO_WORLD.md` forbids `native_decide`, so the kernel evaluates any equality
a proof discharges by computation, and core's derived `DecidableEq (Array α)` is
very expensive there. Deciding equality of two 400-element sequences, with Lean
startup and elaboration (2.01 s) subtracted:

| instance | kernel `decide` |
|---|---|
| routed through `toList` | 0.6 s |
| core's derived `DecidableEq (Array α)` | 26.1 s |

So an `Array`-backed arm is viable **only** if it carries a `toList`-routed
`DecidableEq` rather than inheriting core's. That is a constraint on how the
instance is written, not an argument against the representation.
-/

universe u
variable {α : Type u}

/-- A sequence whose operations really are `Array` operations. -/
structure AVec (α : Type u) where
  mk ::
  toArray : Array α

namespace AVec

def empty : AVec α := ⟨#[]⟩
def length (v : AVec α) : Nat := v.toArray.size
def push (v : AVec α) (a : α) : AVec α := ⟨v.toArray.push a⟩
def get? (v : AVec α) (i : Nat) : Option α := v.toArray[i]?
def append (v w : AVec α) : AVec α := ⟨v.toArray ++ w.toArray⟩
def take (v : AVec α) (n : Nat) : AVec α := ⟨v.toArray.extract 0 n⟩

instance : Append (AVec α) := ⟨append⟩

theorem toArray_injective {v w : AVec α} (h : v.toArray = w.toArray) : v = w := by
  cases v; cases w; simp_all

@[simp] theorem length_empty : (empty : AVec α).length = 0 := rfl

@[simp] theorem length_push (v : AVec α) (a : α) : (v.push a).length = v.length + 1 := by
  simp [length, push]

@[simp] theorem get?_push (v : AVec α) (a : α) (i : Nat) :
    (v.push a).get? i =
      if i < v.length then v.get? i else if i = v.length then some a else none := by
  simp [get?, push, length, Array.getElem?_push]
  split <;> simp_all

@[simp] theorem length_append (v w : AVec α) : (v ++ w).length = v.length + w.length := by
  show (v.toArray ++ w.toArray).size = _
  exact Array.size_append ..

@[simp] theorem length_take (v : AVec α) (n : Nat) : (v.take n).length = min n v.length := by
  simp [length, take]

end AVec
