import Grass.Process.ByteFlow.Egress

/-!
# Rechunking: why chunk boundaries carry no meaning

`docs/PROCESS.md` §3 states the principle in the first sentence of the byte-flow
section:

> The logical payload is an ordered stream of bytes; physical completion
> boundaries are not part of that stream's meaning.

Everything here is that sentence made checkable. A *chunking* is a list of
chunks; what it means is their concatenation; and two chunkings that concatenate
alike are interchangeable to anything that reads the stream rather than the
boundaries.

## What the theorems are actually about

§3 asks for a "carefully scoped functional chunking law", and the scoping is the
interesting part. `ChunkExtensional` below is the scope: a parser qualifies when
its result depends only on the concatenation. A parser that inspected chunk
boundaries — one that treated a chunk edge as a record separator, say — is not
chunk-extensional, and the law does not apply to it and must not.

That is why `parse_is_chunk_blind` takes extensionality as a hypothesis rather
than proving it: it is a property of the parser, not of the stream, and a
version that quietly assumed it would be claiming something false about a real
class of parsers.

## Capacity-aware splitting

`splitForCapacity` is §3's `splitForCapacity`, and the three laws it satisfies
are the ones a credit-limited channel needs:

* **it refines the source** — the concatenation is unchanged, so no byte is
  invented or lost (`splitForCapacity_concat`);
* **every chunk fits** — `EveryChunkFitsCredits` (`splitForCapacity_fits`);
* **no chunk is empty** — §3's `NonemptyByteChunk` is a structure with a
  `nonempty` field, so a splitter that emitted `[]` would produce chunks that
  cannot be sent at all (`splitForCapacity_nonempty`).

The third is the one a naive splitter gets wrong, by emitting a trailing empty
chunk when the stream length is a multiple of the capacity.

## `List` where §3 has `Vec`

`Grass/Process/ByteFlow/Ingress.lean` notes the substitution and flags this
module as where it bites: `Vec` carries its length in the type, so a capacity
law could be stated as a type-level bound rather than as a proof obligation on
every chunk. With `List` the bound is `splitForCapacity_fits`, which is weaker
in exactly one way — it constrains what this splitter produces, not what a
`NonemptyByteChunk` can be. That is the named M3 exit item from §2.1.
-/

namespace Grass.Process

universe u

/--
A chunking of a byte stream: the chunks a provider or channel actually moved.

`docs/PROCESS.md` §3's physical completion boundaries, which the next definition
says carry no meaning.
-/
abbrev Chunking (Byte : Type u) : Type u := List (List Byte)

namespace Chunking

variable {Byte : Type u}

/-- What a chunking means: the stream, boundaries erased. -/
def stream (chunking : Chunking Byte) : List Byte := chunking.flatten

/--
**Two chunkings are equivalent when they mean the same stream.**

§3's "equal after erasing timing, capacity and cancellation cuts". Erasing the
cuts is exactly taking the concatenation, so the relation needs no separate
notion of a cut at all.
-/
def Equivalent (left right : Chunking Byte) : Prop := left.stream = right.stream

theorem equivalent_refl (chunking : Chunking Byte) : Equivalent chunking chunking := rfl

theorem equivalent_symm {left right : Chunking Byte}
    (same : Equivalent left right) : Equivalent right left := same.symm

theorem equivalent_trans {left middle right : Chunking Byte}
    (first : Equivalent left middle) (second : Equivalent middle right) :
    Equivalent left right := first.trans second

/--
Dropping empty chunks changes nothing.

The simplest witness that boundaries carry no meaning: a chunking with empty
chunks in it is equivalent to the one without them, so an implementation that
emits a zero-length completion has not changed what it sent.
-/
theorem equivalent_filter_empty (chunking : Chunking Byte) :
    Equivalent (chunking.filter (fun chunk => !chunk.isEmpty)) chunking := by
  simp only [Equivalent, stream]
  induction chunking with
  | nil => rfl
  | cons chunk rest ih =>
    cases isEmpty : chunk.isEmpty with
    | true =>
      have empty : chunk = [] := by
        cases chunk with
        | nil => rfl
        | cons _ _ => exact absurd isEmpty (by simp)
      simp [List.filter, empty, ih]
    | false => simp [List.filter, isEmpty, ih]

end Chunking

/-! ## Splitting a stream to fit a capacity -/

/--
Split a stream into chunks of at most `capacity` bytes.

`docs/PROCESS.md` §3's `splitForCapacity`. The positivity hypothesis is what
makes it terminate — with a capacity of zero the recursion would never consume
anything, which is also why §3 types the argument as a `PositiveCapacity`.
-/
def splitForCapacity {Byte : Type u} (capacity : Nat) (positive : 0 < capacity) :
    List Byte → Chunking Byte
  | [] => []
  | first :: rest =>
      (first :: rest).take capacity ::
        splitForCapacity capacity positive ((first :: rest).drop capacity)
  termination_by bytes => bytes.length
  decreasing_by
    simp only [List.length_drop, List.length_cons]
    omega

variable {Byte : Type u}

/--
**Splitting refines the source: the stream is unchanged.**

§3's `RefinesWithMappedPrefixAndCancellationCuts`, at the part this layer owns.
No byte is invented, duplicated or lost by rechunking — which is the whole
licence for a channel to choose its own boundaries.
-/
theorem splitForCapacity_stream (capacity : Nat) (positive : 0 < capacity)
    (bytes : List Byte) :
    (splitForCapacity capacity positive bytes).stream = bytes := by
  induction bytes using splitForCapacity.induct capacity positive with
  | case1 => rw [splitForCapacity]; rfl
  | case2 first rest ih =>
    rw [splitForCapacity]
    simp only [Chunking.stream, List.flatten_cons]
    rw [show (splitForCapacity capacity positive ((first :: rest).drop capacity)).flatten
      = (first :: rest).drop capacity from ih]
    exact List.take_append_drop capacity (first :: rest)

/-- So a split is equivalent to the single-chunk chunking of the same stream. -/
theorem splitForCapacity_equivalent (capacity : Nat) (positive : 0 < capacity)
    (bytes : List Byte) :
    Chunking.Equivalent (splitForCapacity capacity positive bytes) [bytes] := by
  simp only [Chunking.Equivalent, Chunking.stream]
  rw [show (splitForCapacity capacity positive bytes).flatten = bytes from
    splitForCapacity_stream capacity positive bytes]
  exact (List.append_nil bytes).symm

/--
**Every chunk fits the capacity.**

§3's `EveryChunkFitsCredits`. This is the half a credit-limited channel needs in
order to send what the splitter produced without a further check.
-/
theorem splitForCapacity_fits (capacity : Nat) (positive : 0 < capacity)
    (bytes : List Byte) :
    ∀ chunk ∈ splitForCapacity capacity positive bytes, chunk.length ≤ capacity := by
  induction bytes using splitForCapacity.induct capacity positive with
  | case1 => intro chunk present; exact absurd present (by simp [splitForCapacity])
  | case2 first rest ih =>
    intro chunk present
    rw [splitForCapacity] at present
    rcases List.mem_cons.mp present with isFirst | inRest
    · rw [isFirst, List.length_take]
      omega
    · exact ih chunk inRest

/--
**And no chunk is empty.**

`docs/PROCESS.md` §3's chunks are `NonemptyByteChunk`s, so a splitter that
emitted `[]` would produce something the channel cannot send. The case that
tempts a naive implementation is a stream whose length is an exact multiple of
the capacity, where a trailing empty chunk is easy to append; the recursion here
stops on the empty list instead.
-/
theorem splitForCapacity_nonempty (capacity : Nat) (positive : 0 < capacity)
    (bytes : List Byte) :
    ∀ chunk ∈ splitForCapacity capacity positive bytes, chunk ≠ [] := by
  induction bytes using splitForCapacity.induct capacity positive with
  | case1 => intro chunk present; exact absurd present (by simp [splitForCapacity])
  | case2 first rest ih =>
    intro chunk present
    rw [splitForCapacity] at present
    rcases List.mem_cons.mp present with isFirst | inRest
    · rw [isFirst]
      intro empty
      have lengthZero := congrArg List.length empty
      simp only [List.length_take, List.length_cons, List.length_nil] at lengthZero
      omega
    · exact ih chunk inRest

/-! ## What a chunk-blind reader sees -/

/--
A parser whose result depends only on the stream, not on the boundaries.

The *scope* of §3's functional chunking law, and a hypothesis rather than a
theorem: a parser that treated a chunk edge as a record separator is a real
thing to write, and the law must not apply to it.
-/
def ChunkExtensional {Result : Type u} (parse : Chunking Byte → Result) : Prop :=
  ∀ left right : Chunking Byte, left.stream = right.stream → parse left = parse right

/--
**A chunk-extensional parser cannot tell two equivalent chunkings apart.**

§3's `parser_chunking_invariant`, and the statement that licenses every
rechunking a channel might perform: the reader's result is unchanged, so the
boundaries were never part of the payload's meaning.
-/
theorem parse_is_chunk_blind {Result : Type u} {parse : Chunking Byte → Result}
    (extensional : ChunkExtensional parse) {left right : Chunking Byte}
    (equivalent : Chunking.Equivalent left right) : parse left = parse right :=
  extensional left right equivalent

/--
So splitting for capacity does not change what a parser reads.

The two halves joined: a channel may split a stream to fit its credits, and a
chunk-extensional reader sees exactly what it would have seen unsplit.
-/
theorem capacity_split_is_invisible {Result : Type u} {parse : Chunking Byte → Result}
    (extensional : ChunkExtensional parse) (capacity : Nat) (positive : 0 < capacity)
    (bytes : List Byte) :
    parse (splitForCapacity capacity positive bytes) = parse [bytes] := by
  exact parse_is_chunk_blind extensional
    (splitForCapacity_equivalent capacity positive bytes)

/--
**A parser that reads boundaries is not chunk-extensional.**

The scope of the law, made visible. `chunkCount` is a perfectly ordinary thing
to compute and it distinguishes two chunkings of the same stream, so it fails
`ChunkExtensional` — which is why the law takes extensionality as a hypothesis
rather than assuming every reader has it.
-/
theorem counting_chunks_is_not_extensional :
    ¬ ChunkExtensional (Byte := Unit) (Result := Nat) (fun chunking => chunking.length) := by
  intro extensional
  have sameStream : Chunking.stream [[(), ()]] = Chunking.stream [[()], [()]] := rfl
  have sameCount := extensional [[(), ()]] [[()], [()]] sameStream
  exact absurd sameCount (by decide)

end Grass.Process
