import Grass.Std.Logical.Vec

/-!
# The `Vec` representation probe

`docs/STDLIB_IMPLEMENTATION_PLAN.md` §3.2 records that a *genuinely* `Array`-backed
`Vec` — one whose `push` is `Array.push` and whose indexing is `Array` indexing,
rather than a rename that keeps `List`-shaped bodies — had been "neither costed nor
probed", and that it is the only candidate able to emit a large artifact. This file
is that probe.

It lived under `Tools/` and `lake` did not build it, which meant an unbuilt file
recording measurements nobody could re-run: the laws could rot against a
toolchain bump without anything failing, and the two tables below cited `#eval`
harnesses that existed only in the author's scratch directory. Both halves are
fixed here. The laws are built like any other fixture, and the benchmark
definitions the tables came from are in the file, compiled but not run --
`#eval` them to reproduce a number rather than trusting it.

It answers three questions and nothing else. The `AVec` laws below are proved without
reference to `Vec` at all -- that independence is half of question one's answer --
while the benchmark section imports `Vec` because comparing against it is the
whole point of the emitter table. It deliberately does **not** define a
replacement for `Grass.Std.Logical.Vec`: §3.2's decision is not this file's to make,
and a probe that shipped a second sequence type would be the churn §6 forbids.

**One: do the laws re-prove against core's `Array` lemmas, without adding a
dependency?** Yes. Every law below is proved from `Array.getElem?_push`,
`Array.size_append` and friends. Mathlib is *permitted* — `docs/MODULES.md` allows
"mathlib and other reviewed Lean dependencies" — and simply is not one today, so
the question is whether the port would force a reviewed dependency addition, not
whether it is allowed one. It would not. This was the open risk — the restatement
cost is only worth paying if the
restatement is possible.

**Two: what does the emitter cost?** `Grass/Std/Logical/Vec.lean`'s `push` is
`⟨v.toList ++ [a]⟩` and its `get?` is `v.toList[i]?`, so building an artifact is
quadratic and reading a byte is linear. The `Array` bodies are amortised constant
and constant. Measured by `#eval`, building by repeated `push` then reading every
index:

| n | `Vec` (`List`-backed) | `AVec` (`Array`-backed) | ratio |
|---|---|---|---|
| 1 000 | 10 ms | 4 ms | 2.5x |
| 4 000 | 99 ms | 2 ms | 50x |
| 16 000 | 1246 ms | 10 ms | 125x |
| 32 000 | 3984 ms | 18 ms | 221x |

`Vec`'s time grows about fourfold per doubling and `AVec`'s about twofold, which is
the quadratic-versus-linear split the definitions predict. Both sides return the
same checksum at every size, so this is two representations doing the same work
rather than one of them skipping it.

**Read the ratio, not the milliseconds.** An earlier run of the same harness
recorded 4 / 63 / 829 / 2890 ms for `Vec` against 2 / 2 / 8 / 14 ms for `AVec` --
the same shape and the same conclusion, with every absolute figure different by up
to 40%. These ran under the Lean interpreter on a loaded developer machine and are
reproducible only to that precision. The finding is the growth exponent and the two
orders of magnitude at n = 32 000; a reader who needs a number for a budget should
re-run `emitterBench` on the machine they care about. `docs/HELLO_WORLD.md`
accepts the milestone only when `emitProgram`'s bytes execute, and `ByteArray` is
`Vec Byte`, so the byte writer runs over this type.

**Three: what does the kernel cost?** This is the axis that cuts the other way.
`docs/HELLO_WORLD.md` forbids `native_decide`, so the kernel evaluates any equality
a proof discharges by computation, and core's derived `DecidableEq (Array α)` is
very expensive there. Deciding equality of two 400-element sequences, timing whole
`lake env lean` runs of this file with one `example` enabled, best of two:

| instance | wall clock | over baseline |
|---|---|---|
| neither example enabled | 2.9 s | — |
| routed through `toList` | 2.1 s | none measurable |
| core's derived `DecidableEq` | 38.6 s | ~36 s |

Baseline varies between 2.9 s and 5.0 s run to run, so the routed instance is
simply indistinguishable from not doing the work at all, while the derived one is
an order of magnitude outside that noise.

**The derived instance does not merely cost time: at default settings it does not
work.** Both examples need `set_option maxRecDepth 100000`; without it the derived
one fails with "maximum recursion depth has been reached" rather than taking a long
time. An earlier version of this section reported 0.6 s and 26.1 s with no mention
of the recursion limit, which made the choice look like a performance trade when
one of the two options does not typecheck as written.

So an `Array`-backed arm is viable **only** if it carries a `toList`-routed
`DecidableEq` rather than inheriting core's. That is a constraint on how the
instance is written, not an argument against the representation.
-/

open Grass.Std.Logical

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

/-! ## The benchmarks the two tables came from

Compiled, so they cannot drift away from the types they measure, and not run,
so a fixture build stays fast. Uncomment an `#eval` to reproduce a row.

### Emitter axis

Build by repeated `push`, then read every index — the shape `emitProgram` has.
-/

/-- The `List`-backed sequence under the emitter's access pattern. -/
def buildReadVec (n : Nat) : IO Nat := do
  let mut v : Vec Nat := Vec.empty
  for i in [0:n] do v := v.push i
  let mut acc := 0
  for i in [0:n] do
    match v.get? i with
    | some x => acc := acc + x
    | none => pure ()
  return acc

/-- The same pattern against `Array` bodies. -/
def buildReadAVec (n : Nat) : IO Nat := do
  let mut v : AVec Nat := AVec.empty
  for i in [0:n] do v := v.push i
  let mut acc := 0
  for i in [0:n] do
    match v.get? i with
    | some x => acc := acc + x
    | none => pure ()
  return acc

/-- Wall-clock around one run. The checksum is printed so a run that silently
did nothing is distinguishable from a fast one. -/
def timed (label : String) (f : IO Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r ← f
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1 - t0} ms (checksum {r})"

/-- Every row of the emitter table. -/
def emitterBench : IO Unit := do
  for n in [1000, 4000, 16000, 32000] do
    timed s!"Vec  n={n}" (buildReadVec n)
    timed s!"AVec n={n}" (buildReadAVec n)

-- #eval emitterBench

/-! ### Kernel axis

`docs/HELLO_WORLD.md` forbids `native_decide`, so the kernel evaluates any
equality a proof discharges by computation. `AVec`'s instance routes through
`List`; `KVec` is the same structure taking core's derived instance, and exists
only to be the comparison. Time `lake env lean` on a file asserting each
`example`, and subtract a run with both commented out — startup and elaboration
were 2.01 s when these numbers were taken.
-/

/-- The `toList`-routed instance, which is what the costing says an `Array` arm
would have to carry. -/
instance [DecidableEq α] : DecidableEq (AVec α) := fun v w =>
  if h : v.toArray.toList = w.toArray.toList then
    .isTrue (by cases v; cases w; simp_all)
  else .isFalse (by intro e; exact h (by rw [e]))

/-- The same data taking core's derived instance, for comparison only. -/
structure KVec (α : Type u) where
  mk ::
  toArray : Array α
deriving DecidableEq

def bigAVec : AVec Nat := ⟨(List.range 400).toArray⟩
def bigAVec' : AVec Nat := ⟨(List.range 400).toArray⟩
def bigKVec : KVec Nat := ⟨(List.range 400).toArray⟩
def bigKVec' : KVec Nat := ⟨(List.range 400).toArray⟩

-- set_option maxRecDepth 100000 in
-- example : bigAVec = bigAVec' := by decide   -- baseline-indistinguishable
-- set_option maxRecDepth 100000 in
-- example : bigKVec = bigKVec' := by decide   -- ~36 s over baseline

end AVec
