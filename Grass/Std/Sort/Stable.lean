import Grass.Std.Sort.Descriptors
import Init.Data.List.Sort

/-!
# A reusable bottom-up stable merge sort model

`Grass.Std.Logical.Vec.stableSort` (`Grass/Std/Logical/StableSort.lean`) delegates
to Lean core's `List.mergeSort`, which splits its input top-down; it deliberately
does not model an authored bottom-up runtime loop. Spike 2 (Sort)'s assembly
implements an *iterative* bottom-up merge sort: passes with run width
`1, 2, 4, ...` merge adjacent runs from a source array into a scratch array,
then the two arrays swap roles for the next pass. This module supplies that
executable model and proves it a stable sort, reusing Lean core's proved
two-way `List.merge` (`Init.Data.List.Sort.Lemmas`) as the merge primitive
rather than re-deriving merge correctness.

Stability is stated over *occurrences* -- an element paired with its original
position -- rather than over bare values, because a position-free statement is
either unsatisfiable (indexing by value collapses duplicates to one position)
or vacuous. `Grass.Std.Logical.Order`'s `Vec.Permutation`/`Vec.Pairwise`/
`Vec.idxOf?` supply the same vocabulary `Spikes/2_Sort/Spec.lean`'s
`stableSorted` is written in; `contract` below is that specification,
generalized over the element type and comparator. Occurrences here are
`α × Nat` (value, ordinal), matching Lean core's `List.zipIdx`/`List.zipIdxLE`
convention so their transitivity/totality lemmas transfer without restatement;
`Grass.Std.Sort.DescriptorSort.Occurrence` and `Spikes/2_Sort/Spec.lean`'s
`Occurrence` instead write `(ordinal, value)`, so callers crossing that
boundary swap the pair.
-/

namespace Grass.Std.Sort

open Grass.Std.Logical

namespace StableSort

universe u

variable {α : Type u}

/-! ## Bottom-up merge passes

`mergePass` is one pass: adjacent runs are merged pairwise, halving the run
count (an odd final run carries over untouched). `bottomUpPasses` repeats
passes until one run remains, which is exactly `sort_pass`'s loop in
`Spikes/2_Sort/Assembly.lean` -- each call is a full source/scratch pass, and
consecutive calls play the role of the buffer swap (`xchg rdi, rsi`). -/

/-- One bottom-up merge pass over a list of already-sorted runs: adjacent runs
are merged with `List.merge`, and a trailing unpaired run is carried through
unchanged. This is the "current pass, scratch array" step. -/
def mergePass (le : α → α → Bool) : List (List α) → List (List α)
  | [] => []
  | [run] => [run]
  | left :: right :: rest => List.merge left right le :: mergePass le rest

theorem length_mergePass (le : α → α → Bool) :
    ∀ runs : List (List α), (mergePass le runs).length = (runs.length + 1) / 2
  | [] => by simp [mergePass]
  | [_] => by simp [mergePass]
  | _ :: _ :: rest => by
      have ih := length_mergePass le rest
      simp only [mergePass, List.length_cons, ih]
      omega

/-- A pass strictly shrinks the run count whenever there is more than one run
to merge -- the measure `Spikes/2_Sort/Assembly.lean` calls
`merge_pass_measure`. -/
theorem mergePass_length_lt (le : α → α → Bool) {runs : List (List α)}
    (h : 2 ≤ runs.length) : (mergePass le runs).length < runs.length := by
  rw [length_mergePass]
  omega

/-- Repeated bottom-up merge passes until one run remains: the assembly's
`sort_pass` loop, terminating when the run width reaches the record count. -/
def bottomUpPasses (le : α → α → Bool) : List (List α) → List α
  | [] => []
  | [run] => run
  | left :: right :: rest =>
      bottomUpPasses le (mergePass le (left :: right :: rest))
termination_by runs => runs.length
decreasing_by exact mergePass_length_lt le (by simp)

/-- The bottom-up merge sort model: partition into singleton runs (pass width
`1`) and merge passes until sorted. -/
def bottomUpMergeList (le : α → α → Bool) (xs : List α) : List α :=
  bottomUpPasses le (xs.map fun x => [x])

/-! ## Sortedness

Ported from core's two-way `merge` sortedness (`List.pairwise_merge`), not
re-derived: a pass keeps every run pairwise-`le`, so the one run left after
every pass does too. -/

theorem pairwise_mergePass (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) :
    ∀ (runs : List (List α)),
      (∀ run ∈ runs, run.Pairwise (fun a b => le a b = true)) →
      ∀ run ∈ mergePass le runs, run.Pairwise (fun a b => le a b = true)
  | [], _ => by simp [mergePass]
  | [_], h => by simpa [mergePass] using h
  | left :: right :: rest, h => by
      intro run hrun
      simp only [mergePass, List.mem_cons] at hrun
      rcases hrun with rfl | hrun
      · exact List.pairwise_merge trans total left right
          (h left (List.mem_cons_self ..))
          (h right (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      · exact pairwise_mergePass le trans total rest
          (fun r hr => h r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) run hrun

theorem pairwise_bottomUpPasses (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) :
    ∀ (runs : List (List α)),
      (∀ run ∈ runs, run.Pairwise (fun a b => le a b = true)) →
      (bottomUpPasses le runs).Pairwise (fun a b => le a b = true)
  | [], _ => by simp [bottomUpPasses]
  | [run], h => by simpa [bottomUpPasses] using h run (List.mem_cons_self ..)
  | left :: right :: rest, h => by
      have hpass := pairwise_mergePass le trans total (left :: right :: rest) h
      have hrec :=
        pairwise_bottomUpPasses le trans total (mergePass le (left :: right :: rest)) hpass
      simpa [bottomUpPasses] using hrec
termination_by runs _ => runs.length
decreasing_by exact mergePass_length_lt le (by simp)

/-- The model is pairwise `le`-sorted: `StableSort.contract`'s `sorted`
conjunct, reusing `List.pairwise_merge` at every pass rather than re-proving
merge sortedness. -/
theorem bottomUpMergeList_pairwise (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) (xs : List α) :
    (bottomUpMergeList le xs).Pairwise (fun a b => le a b = true) := by
  apply pairwise_bottomUpPasses le trans total
  intro run hrun
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hrun
  exact List.pairwise_singleton ..

/-! ## Permutation

Ported from core's `List.merge_perm_append`, not re-derived: a pass rearranges
each pair of runs without losing or inventing elements, so it rearranges the
whole concatenation, and so does the loop of passes. -/

theorem mergePass_flatten_perm (le : α → α → Bool) :
    ∀ (runs : List (List α)), (mergePass le runs).flatten.Perm runs.flatten
  | [] => by simp [mergePass]
  | [_] => by simp [mergePass]
  | left :: right :: rest => by
      have htail := mergePass_flatten_perm le rest
      have hmerge : (List.merge left right le).Perm (left ++ right) :=
        List.merge_perm_append le
      have hstep := hmerge.append htail
      rw [List.append_assoc] at hstep
      simpa only [mergePass, List.flatten_cons] using hstep

theorem bottomUpPasses_perm (le : α → α → Bool) :
    ∀ (runs : List (List α)), (bottomUpPasses le runs).Perm runs.flatten
  | [] => by simp [bottomUpPasses]
  | [_] => by simp [bottomUpPasses]
  | left :: right :: rest => by
      have h1 := bottomUpPasses_perm le (mergePass le (left :: right :: rest))
      have h2 := mergePass_flatten_perm le (left :: right :: rest)
      have hrw : bottomUpPasses le (left :: right :: rest) =
          bottomUpPasses le (mergePass le (left :: right :: rest)) := by
        simp [bottomUpPasses]
      rw [hrw]
      exact h1.trans h2
termination_by runs => runs.length
decreasing_by exact mergePass_length_lt le (by simp)

theorem flatten_map_singleton (xs : List α) : (xs.map fun x => [x]).flatten = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- The model rearranges its input: `StableSort.contract`'s `perm` conjunct. -/
theorem bottomUpMergeList_perm (le : α → α → Bool) (xs : List α) :
    (bottomUpMergeList le xs).Perm xs := by
  have h := bottomUpPasses_perm le (xs.map fun x => [x])
  rwa [flatten_map_singleton] at h

theorem length_bottomUpMergeList (le : α → α → Bool) (xs : List α) :
    (bottomUpMergeList le xs).length = xs.length :=
  (bottomUpMergeList_perm le xs).length_eq

/-! ## Stability

An input decorated with its own position (`List.zipIdx`, giving `α × Nat`
"occurrences" of `(value, ordinal)`) and sorted by core's lexicographic
`List.zipIdxLE le` is sorted by `le` on values *and* by ordinal wherever two
values are `le`-equivalent -- both read off the single `Pairwise (zipIdxLE le)`
fact below by unfolding `zipIdxLE`, so stability costs no new sort proof. This
ports the same device core itself uses to state `mergeSort`'s stability
(`List.mergeSort_zipIdx`, `List.merge_stable`), applied to `bottomUpMergeList`
instead of `List.mergeSort`, and reuses `List.zipIdxLE_trans`/`_total` so the
comparator's transitivity/totality need not be re-derived at the pair type. -/

/-- The model applied to ordinal-decorated occurrences: ties are broken by
original position, which is the mathematical content of the assembly's merge
choosing the left (earlier) run on `compare = 0` (`jle .merge_take_left`). -/
def bottomUpMergeOccurrences (le : α → α → Bool) (xs : List α) : List (α × Nat) :=
  bottomUpMergeList (List.zipIdxLE le) xs.zipIdx

theorem bottomUpMergeOccurrences_perm (le : α → α → Bool) (xs : List α) :
    (bottomUpMergeOccurrences le xs).Perm xs.zipIdx :=
  bottomUpMergeList_perm (List.zipIdxLE le) xs.zipIdx

theorem bottomUpMergeOccurrences_pairwise (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) (xs : List α) :
    (bottomUpMergeOccurrences le xs).Pairwise (fun a b => List.zipIdxLE le a b = true) :=
  bottomUpMergeList_pairwise (List.zipIdxLE le)
    (List.zipIdxLE_trans trans) (List.zipIdxLE_total total) xs.zipIdx

/-- An occurrence pair ordered by `zipIdxLE le` has `le`-ordered values --
half of `StableSort.contract`'s `sorted` conjunct once occurrences are
projected to values. -/
theorem le_of_zipIdxLE {le : α → α → Bool} {a b : α × Nat}
    (h : List.zipIdxLE le a b = true) : le a.1 b.1 = true := by
  simp only [List.zipIdxLE] at h
  split at h
  · assumption
  · simp at h

/-- An occurrence pair ordered by `zipIdxLE le` whose values are also
`le`-equivalent the other way keeps input order on their ordinals -- the
stability half of `zipIdxLE`. -/
theorem ordinal_le_of_zipIdxLE {le : α → α → Bool} {a b : α × Nat}
    (h : List.zipIdxLE le a b = true) (hba : le b.1 a.1 = true) : a.2 ≤ b.2 := by
  simp only [List.zipIdxLE, hba, if_pos] at h
  split at h
  · simpa using h
  · simp_all

/-- The model's occurrences are `le`-sorted by value: `StableSort.contract`'s
`sorted` conjunct. -/
theorem bottomUpMergeOccurrences_sorted (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) (xs : List α) :
    (bottomUpMergeOccurrences le xs).Pairwise (fun a b => le a.1 b.1 = true) :=
  (bottomUpMergeOccurrences_pairwise le trans total xs).imp le_of_zipIdxLE

/-- **Stability by position.** Two `le`-equivalent occurrences at output
positions `p, q` keep their ordinal order: `p < q` iff their ordinals do. This
is `StableSort.contract`'s `stable` conjunct stated on the model's own output
list, before any `Vec`/`idxOf?` packaging. -/
theorem bottomUpMergeOccurrences_stable (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) {xs : List α}
    {p q : Nat} (hp : p < (bottomUpMergeOccurrences le xs).length)
    (hq : q < (bottomUpMergeOccurrences le xs).length)
    (hle : le ((bottomUpMergeOccurrences le xs)[p]'hp).1
        ((bottomUpMergeOccurrences le xs)[q]'hq).1 = true)
    (hge : le ((bottomUpMergeOccurrences le xs)[q]'hq).1
        ((bottomUpMergeOccurrences le xs)[p]'hp).1 = true)
    (hlt : ((bottomUpMergeOccurrences le xs)[p]'hp).2
        < ((bottomUpMergeOccurrences le xs)[q]'hq).2) :
    p < q := by
  rcases Nat.lt_or_ge p q with hpq | hqp
  · exact hpq
  · exfalso
    have hpw := bottomUpMergeOccurrences_pairwise le trans total xs
    rcases Nat.lt_or_eq_of_le hqp with hqp' | heq
    · have hrel := (List.pairwise_iff_getElem.mp hpw) q p hq hp hqp'
      have hord := ordinal_le_of_zipIdxLE hrel hle
      omega
    · subst heq
      exact absurd hlt (Nat.lt_irrefl _)

/-! ## The contract, and the model's `Vec` packaging

`Spikes/2_Sort/Spec.lean`'s `stableSorted` reads directly off
`Grass.Std.Logical.Order`'s `Vec.Permutation`/`Vec.Pairwise`/`Vec.idxOf?`; this
is that same shape, generalized over the element type and comparator, and
already occurrence-shaped so it is satisfiable on inputs holding repeated
values (`docs/SPIKE_2.md` §5 and this module's header explain why ordinals,
not bare values, key stability). -/

/-- The stable-sort contract: `output` is a permutation of `input`'s
occurrences, `le`-sorted, and any two `le`-equivalent occurrences keep the
input order of their ordinals at their output positions. -/
def contract [BEq α] (le : α → α → Bool) (input output : Vec (α × Nat)) : Prop :=
  output.Permutation input ∧
  output.Pairwise (fun a b => le a.1 b.1 = true) ∧
  ∀ (i j : Nat) (hi : i < input.length) (hj : j < input.length),
    le (input.get i hi).1 (input.get j hj).1 = true →
    le (input.get j hj).1 (input.get i hi).1 = true →
    (input.get i hi).2 < (input.get j hj).2 →
    ∀ p q, output.idxOf? (input.get i hi) = some p →
           output.idxOf? (input.get j hj) = some q →
           p < q

/-- The occurrence-decorated view of a `Vec`: each element paired with its
position, matching `List.zipIdx`. -/
def occurrences (input : Vec α) : Vec (α × Nat) := Vec.fromList input.toList.zipIdx

/-- The bottom-up merge sort model, packaged over `Vec` -- the reusable
substitute for `StableSort.bottomUpMergeModel` in `Spikes/2_Sort/Assembly.lean`
(that name additionally carries an `ImplementationModel` wrapper this library
does not supply; see the module report). -/
def bottomUpMergeModel (le : α → α → Bool) (input : Vec α) : Vec (α × Nat) :=
  Vec.fromList (bottomUpMergeOccurrences le input.toList)

theorem length_bottomUpMergeModel (le : α → α → Bool) (input : Vec α) :
    (bottomUpMergeModel le input).length = input.length := by
  have h := (bottomUpMergeOccurrences_perm le input.toList).length_eq
  simpa [bottomUpMergeModel, Vec.length] using h

/-- **The model satisfies the contract.** Everything here transports a
`List`-level fact already proved above -- `bottomUpMergeOccurrences_perm`,
`_sorted`, `_stable` -- through the `Vec`/`idxOf?` packaging
`Spikes/2_Sort/Spec.lean` is written in; no sortedness, permutation, or
stability fact is re-derived at this layer. -/
theorem bottomUpMergeCorrect [BEq α] [LawfulBEq α] (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) (input : Vec α) :
    contract le (occurrences input) (bottomUpMergeModel le input) := by
  refine ⟨?_, ?_, ?_⟩
  · exact bottomUpMergeOccurrences_perm le input.toList
  · exact bottomUpMergeOccurrences_sorted le trans total input.toList
  · intro i j hi hj hle hge hlt p q hp hq
    obtain ⟨hip, hival, -⟩ := Vec.idxOf?_eq_some hp
    obtain ⟨hjp, hjval, -⟩ := Vec.idxOf?_eq_some hq
    have hip' : p < (bottomUpMergeOccurrences le input.toList).length := by
      simpa [bottomUpMergeModel] using hip
    have hjp' : q < (bottomUpMergeOccurrences le input.toList).length := by
      simpa [bottomUpMergeModel] using hjp
    have hgetp : (bottomUpMergeOccurrences le input.toList)[p]'hip' =
        (occurrences input).get i hi := by
      simpa [bottomUpMergeModel, Vec.get] using hival
    have hgetq : (bottomUpMergeOccurrences le input.toList)[q]'hjp' =
        (occurrences input).get j hj := by
      simpa [bottomUpMergeModel, Vec.get] using hjval
    apply bottomUpMergeOccurrences_stable le trans total (xs := input.toList) hip' hjp'
    · rw [hgetp, hgetq]; exact hle
    · rw [hgetp, hgetq]; exact hge
    · rw [hgetp, hgetq]; exact hlt

/-! ## The line/descriptor array representation

`Grass.Std.Sort.Descriptors` already relates a byte source and a descriptor
array to the stable sort of the decoded lines it selects, keyed on byte-
lexicographic order (`DescriptorSort.sort`, built on `Vec.stableSort`/core
`List.mergeSort` -- see that file's header, which explains it is "not ... a
refinement of the authored bottom-up merge loops"). `lineDescriptorArrayRepresentation`
restates that same connection in `contract`'s vocabulary, so either sort
algorithm's descriptor output can be checked against one specification. No
permutation, order, or stability fact about descriptors is re-derived below;
every step composes `DescriptorSort`'s own theorems
(`decoded_permutation_sort`, `decoded_ordered_sort`, `stable_equal_bytes`)
through the `(value, ordinal)`/`(ordinal, value)` pair-order swap documented
at the top of this file. -/

/-- `Vec.idxOf?` under a bijective, `BEq`-respecting reindexing: searching a
swapped list for a swapped element is the same search. A short, self-contained
step (not in `Init.Data.List.Sort`) needed only to move `DescriptorSort`'s
`(ordinal, value)` stability facts into `contract`'s `(value, ordinal)` shape. -/
theorem idxOf?_swap {γ δ : Type} [BEq γ] [BEq δ] (l : List (γ × δ)) (x : γ × δ) :
    (l.map Prod.swap).idxOf? x.swap = l.idxOf? x := by
  simp only [List.idxOf?, List.findIdx?_map]
  congr 1
  funext y
  show ((y.2 == x.2) && (y.1 == x.1)) = ((y.1 == x.1) && (y.2 == x.2))
  exact Bool.and_comm _ _

private theorem eq_of_map_toNat_eq : ∀ {left right : List Byte},
    left.map BitVec.toNat = right.map BitVec.toNat → left = right
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by simp at h
  | _ :: _, [] => fun h => by simp at h
  | a :: as, b :: bs => fun h => by
      simp only [List.map_cons, List.cons.injEq] at h
      have ha : a = b := BitVec.toNat_inj.mp h.1
      have hrest : as = bs := eq_of_map_toNat_eq h.2
      rw [ha, hrest]

/-- Unsigned lexicographic byte order is antisymmetric. `ByteOrder.lean`
states its preorder laws (`lexicographicLE_trans`/`_total`) but not this one,
which the stability conjunct below needs to read a `le`-both-ways occurrence
pair as one equal-key pair, matching `DescriptorSort.stable_equal_bytes`'s
`equal` hypothesis. -/
theorem lexicographicLE_antisymm {left right : Vec Byte}
    (hlr : ByteArray.lexicographicLE left right = true)
    (hrl : ByteArray.lexicographicLE right left = true) : left = right := by
  simp only [ByteArray.lexicographicLE, decide_eq_true_eq] at hlr hrl
  have heq : left.toList.map BitVec.toNat = right.toList.map BitVec.toNat :=
    List.le_antisymm hlr hrl
  exact Vec.toList_injective (eq_of_map_toNat_eq heq)

/-- The occurrence view of a byte source and a descriptor array selecting
lines from it, in `contract`'s `(value, ordinal)` shape.
`DescriptorSort.Occurrence` and `Spikes/2_Sort/Spec.lean`'s `Occurrence`
instead write `(ordinal, value)`; see this file's header. -/
def lineDescriptorArrayRepresentation (source : Vec Byte) (descriptors : Vec Descriptor) :
    Vec (Vec Byte × Nat) :=
  descriptors.mapIdx fun ordinal descriptor => (descriptor.bytes source, ordinal)

/-- The descriptor sort's decoded output, in the same occurrence shape. -/
def lineDescriptorSortResult (source : Vec Byte) (descriptors : Vec Descriptor) :
    Vec (Vec Byte × Nat) :=
  (DescriptorSort.sort source descriptors).map (fun occurrence => (occurrence.2.bytes source, occurrence.1))

private theorem lineDescriptorSortResult_swap (source : Vec Byte) (descriptors : Vec Descriptor) :
    (lineDescriptorSortResult source descriptors).toList =
      (((DescriptorSort.sort source descriptors).map
        (DescriptorSort.decode source)).toList).map Prod.swap := by
  simp [lineDescriptorSortResult, Vec.map, DescriptorSort.decode, List.map_map, Function.comp]

/-- **The descriptor sort of the array corresponds to the stable sort of the
represented lines.** Composed entirely from `Grass.Std.Sort.DescriptorSort`'s
own permutation, order, and stability theorems; the reusable substitute for
`StableSort.lineDescriptorArrayRepresentation` in `Spikes/2_Sort/Assembly.lean`
(that name additionally carries a `RepresentationPlan` wrapper this library
does not supply; see the module report). -/
theorem lineDescriptorArrayRepresentation_contract
    (source : Vec Byte) (descriptors : Vec Descriptor) :
    contract ByteArray.lexicographicLE
      (lineDescriptorArrayRepresentation source descriptors)
      (lineDescriptorSortResult source descriptors) := by
  refine ⟨?_, ?_, ?_⟩
  · show (lineDescriptorSortResult source descriptors).toList.Perm
      (lineDescriptorArrayRepresentation source descriptors).toList
    have h := DescriptorSort.decoded_permutation_sort source descriptors
    have hL := lineDescriptorSortResult_swap source descriptors
    have hR : (lineDescriptorArrayRepresentation source descriptors).toList =
        (((descriptors.mapIdx fun ordinal descriptor => (ordinal, descriptor)).map
          (DescriptorSort.decode source)).toList).map Prod.swap := by
      simp [lineDescriptorArrayRepresentation, Vec.map, Vec.mapIdx, List.mapIdx_eq_zipIdx_map,
        DescriptorSort.decode, List.map_map, Function.comp]
    rw [hL, hR]
    exact List.Perm.map Prod.swap h
  · show (lineDescriptorSortResult source descriptors).toList.Pairwise
      (fun a b => ByteArray.lexicographicLE a.1 b.1 = true)
    have h := DescriptorSort.decoded_ordered_sort source descriptors
    rw [lineDescriptorSortResult_swap, List.pairwise_map]
    exact h
  · intro i j hi hj hle hge hlt p q hp hq
    have hi' : i < descriptors.length := by
      simpa [lineDescriptorArrayRepresentation, Vec.mapIdx, Vec.length] using hi
    have hj' : j < descriptors.length := by
      simpa [lineDescriptorArrayRepresentation, Vec.mapIdx, Vec.length] using hj
    have hget_i : (lineDescriptorArrayRepresentation source descriptors).get i hi =
        ((descriptors.get i hi').bytes source, i) := by
      simp only [lineDescriptorArrayRepresentation, Vec.get, Vec.mapIdx, List.getElem_mapIdx]
      rfl
    have hget_j : (lineDescriptorArrayRepresentation source descriptors).get j hj =
        ((descriptors.get j hj').bytes source, j) := by
      simp only [lineDescriptorArrayRepresentation, Vec.get, Vec.mapIdx, List.getElem_mapIdx]
      rfl
    rw [hget_i, hget_j] at hle hge hlt
    have hequal : (descriptors.get i hi').bytes source = (descriptors.get j hj').bytes source :=
      lexicographicLE_antisymm hle hge
    have hp' : ((DescriptorSort.sort source descriptors).map (DescriptorSort.decode source)).idxOf?
        (i, (descriptors.get i hi').bytes source) = some p := by
      have hpre : (lineDescriptorSortResult source descriptors).idxOf?
          ((descriptors.get i hi').bytes source, i) = some p := by
        rw [← hget_i]; exact hp
      have hstep : (((DescriptorSort.sort source descriptors).map
          (DescriptorSort.decode source)).toList.map Prod.swap).idxOf?
          ((descriptors.get i hi').bytes source, i) = some p := by
        rw [← lineDescriptorSortResult_swap]; exact hpre
      have hswap : ((descriptors.get i hi').bytes source, i) =
          (i, (descriptors.get i hi').bytes source).swap := rfl
      rw [hswap, idxOf?_swap] at hstep
      exact hstep
    have hq' : ((DescriptorSort.sort source descriptors).map (DescriptorSort.decode source)).idxOf?
        (j, (descriptors.get j hj').bytes source) = some q := by
      have hpre : (lineDescriptorSortResult source descriptors).idxOf?
          ((descriptors.get j hj').bytes source, j) = some q := by
        rw [← hget_j]; exact hq
      have hstep : (((DescriptorSort.sort source descriptors).map
          (DescriptorSort.decode source)).toList.map Prod.swap).idxOf?
          ((descriptors.get j hj').bytes source, j) = some q := by
        rw [← lineDescriptorSortResult_swap]; exact hpre
      have hswap : ((descriptors.get j hj').bytes source, j) =
          (j, (descriptors.get j hj').bytes source).swap := rfl
      rw [hswap, idxOf?_swap] at hstep
      exact hstep
    exact DescriptorSort.stable_equal_bytes source descriptors i j hi' hj' hlt hequal hp' hq'

end StableSort
end Grass.Std.Sort
