import Grass.Std.Logical.Vec

/-!
# The `Vec` operations the authored spike surface actually calls

`Spikes/README.md` holds the comment-free expected author source for the five
design spikes, and `docs/SPIKE_AUTHORING.md` makes those files the reviewed
statement of what an author is expected to write. They are therefore the closest
thing this library has to a named consumer: everything else in
`docs/STDLIB.md` §3 is an interface list, but a spike is someone writing the
call.

`Grass/Std/Logical/Vec.lean`'s deliberate absences are justified by "no consumer
has demanded it". That justification is only honest if the corpus has been read
for demands rather than assumed to have none. This fixture is that reading,
compiled: every `Vec` operation the spike sources call is exercised here in the
shape they call it, over stand-in types, because the real ones
(`RawInstruction`, `Operand`, `CString`, `StackObjectSpec`) belong to layers that
do not exist yet.

What the reading found, in `Spikes/5_Spinning_Cube/Macros.lean` and
`Layout.lean`: `Vec.zipWith` at the exact argument order used here,
`Vec.mapIdx`, `Vec.map` through dot notation, `++`, and array-literal syntax.
The first four are exercised below. The fifth is not, and §"Literal syntax"
records why.
-/

namespace Grass.Tests.Std

open Grass.Std.Logical

/-! ## Stand-in types

Deliberately minimal. The point is the container's surface, not these.
-/

/-- A stand-in for `Operand`. -/
inductive Operand where
  | immediate (value : Nat)
  | register (index : Nat)
  deriving DecidableEq

/-- A stand-in for `CallLocation`. -/
inductive CallLocation where
  | register (index : Nat)
  | stack (offset : Nat)
  deriving DecidableEq

/-- A stand-in for `RawInstruction`. -/
inductive RawInstruction where
  | mov (destination : Nat) (source : Operand)
  | load (destination : Nat) (address : Nat)
  deriving DecidableEq

/-! ## `Vec.zipWith`

`Spikes/5_Spinning_Cube/Macros.lean` writes:

```text
def expandLoad (destinations : Vec Register) (sources : Vec Address) :
    Vec RawInstruction :=
  Vec.zipWith (fun destination source => .mov destination (.memory source))
    destinations sources
```

The argument order is `Vec.zipWith f v w` with the function first and both
sequences after, which is the order `Vec.zipWith` takes.
-/

def expandLoad (destinations : Vec Nat) (sources : Vec Nat) : Vec RawInstruction :=
  Vec.zipWith (fun destination source => .load destination source) destinations sources

/-- The spike calls this with equal-length sequences, but nothing in the type says
so, and `Vec.length_zipWith` is what says what happens when they differ: the
result is the shorter one. A caller that needs the lengths equal has to say so. -/
theorem expandLoad_length (destinations sources : Vec Nat) :
    (expandLoad destinations sources).length = min destinations.length sources.length :=
  Vec.length_zipWith _ destinations sources

example :
    (expandLoad (Vec.fromList [1, 2]) (Vec.fromList [10, 20, 30])).toList
      = [.load 1 10, .load 2 20] := rfl

/-! ## `Vec.mapIdx`

`Spikes/5_Spinning_Cube/Macros.lean` writes:

```text
def expandArguments (arguments : Vec Operand) : Vec RawInstruction :=
  ParallelMove.expand
    (arguments.mapIdx fun index argument =>
      (argument, win64ArgLocation index))
```

Dot notation has to place `arguments` in the sequence argument of
`Vec.mapIdx f v`, and the index has to be the element's position.
-/

def win64ArgLocation : Nat → CallLocation
  | 0 => .register 1
  | 1 => .register 2
  | 2 => .register 8
  | 3 => .register 9
  | n + 4 => .stack (32 + 8 * n)

def pairWithLocation (arguments : Vec Operand) : Vec (Operand × CallLocation) :=
  arguments.mapIdx fun index argument => (argument, win64ArgLocation index)

/-- The index `mapIdx` passes is the position the element is read back at, which is
what makes the calling-convention assignment above correct rather than merely
plausible. -/
theorem pairWithLocation_at (arguments : Vec Operand) (i : Nat) :
    (pairWithLocation arguments).get? i
      = (arguments.get? i).map (fun a => (a, win64ArgLocation i)) :=
  Vec.get?_mapIdx _ arguments i

example :
    (pairWithLocation (Vec.fromList [.immediate 7, .register 3])).toList
      = [(.immediate 7, .register 1), (.register 3, .register 2)] := rfl

/-! ## `Vec.map` through dot notation, and `++`

`Spikes/5_Spinning_Cube/Macros.lean` writes `fields.map fun field => ...` and
chains results with `++`. Dot notation must reach `Vec.map f v` with `fields` in
the sequence position even though `f` comes first.
-/

def expandStore (destinations : Vec Nat) : Vec RawInstruction :=
  destinations.map fun destination => .mov destination (.immediate 0)

def expandBoth (destinations sources : Vec Nat) : Vec RawInstruction :=
  expandStore destinations ++ expandLoad destinations sources

example :
    (expandBoth (Vec.fromList [1]) (Vec.fromList [10])).toList
      = [.mov 1 (.immediate 0), .load 1 10] := rfl

/-- Appending concatenates rather than interleaving, which is what lets a macro
expander build an instruction burst by concatenating fragments. -/
theorem expandBoth_length (destinations sources : Vec Nat) :
    (expandBoth destinations sources).length
      = destinations.length + min destinations.length sources.length := by
  simp [expandBoth, expandStore, expandLoad]

/-! ## Literal syntax: the one demanded operation this library does not provide

The spike sources write `Vec` literals with array-literal syntax — seven
ascribed sites in `Spikes/5_Spinning_Cube/Layout.lean` and `Macros.lean`, plus
`#[]` as a `Vec` result and `#[...]` as an operand of `++`. This library has no
such notation, so every literal in this fixture is written `Vec.fromList [...]`
instead, and the spike surface does not yet elaborate.

That gap is deliberate rather than overlooked, and
`docs/STDLIB_IMPLEMENTATION_PLAN.md` §3.5 records the three mechanisms that were
tried and measured before it was left open. The short version is that the
obvious one is actively harmful: a `macro_rules` for `#[...]` does not overload
with Lean's array literal, it shadows it, so `Array` literals stop elaborating in
every module that transitively imports this one. Shipping notation that breaks
another agent's `Array` code to save this library some punctuation is not a
trade this owner gets to make quietly, and the authored spike surface belongs to
`docs/SPIKE_AUTHORING.md` rather than to this library in any case.

The two examples below are what the corresponding spike lines have to be written
as today. They are here so that the gap is visible in compiled code rather than
only in a plan.
-/

/-- `Spikes/5_Spinning_Cube/Layout.lean:10` writes this as
`def deviceExtensionNames : Vec CString := #["VK_KHR_swapchain"]`. -/
def deviceExtensionNames : Vec String := Vec.fromList ["VK_KHR_swapchain"]

/-- `Spikes/5_Spinning_Cube/Macros.lean:23` writes the `none` branch as `#[]`. -/
def resultMove : Option Nat → Vec RawInstruction
  | none => Vec.empty
  | some destination => Vec.fromList [.mov destination (.immediate 0)]

example : (resultMove none).length = 0 := rfl

end Grass.Tests.Std
