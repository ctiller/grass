import Grass.Grammar.Realization

/-!
# Chunk-invariant streaming parser interface

`StreamingParser.rechunk` connects an incremental state machine to one realized
finite-buffer parser; `StreamingParser.finish_eq_of_flatten_eq` is the theorem
that equal flattened transports have equal completed results.
-/

namespace Grass.Grammar

open Grass.Std.Logical

universe u

/-- A streaming state machine whose completed result is exactly the result of
one finite-buffer parser over the flattened input chunks. -/
structure StreamingParser {α : Type u}
    (parse : Std.Logical.ByteArray → ParseResult α) where
  State : Type
  initial : State
  feed : State → Std.Logical.ByteArray → State
  finish : State → ParseResult α
  rechunk : ∀ chunks : Vec Std.Logical.ByteArray,
    finish (chunks.foldl feed initial) = parse (Vec.flatten chunks)

namespace StreamingParser

/-- Feed every chunk in arrival order. -/
def feedAll {α : Type u} {parse : Std.Logical.ByteArray → ParseResult α}
    (stream : StreamingParser parse)
    (chunks : Vec Std.Logical.ByteArray) : stream.State :=
  chunks.foldl stream.feed stream.initial

/-- Two chunk sequences with the same flattened bytes have the same completed
stream result. -/
theorem finish_eq_of_flatten_eq {α : Type u}
    {parse : Std.Logical.ByteArray → ParseResult α}
    (stream : StreamingParser parse)
    {left right : Vec Std.Logical.ByteArray}
    (sameBytes : Vec.flatten left = Vec.flatten right) :
    stream.finish (stream.feedAll left) = stream.finish (stream.feedAll right) := by
  rw [feedAll, feedAll, stream.rechunk, stream.rechunk, sameBytes]

/-- Finishing any chunking gives the finite parser's result on the named byte
sequence. -/
theorem finish_of_isChunking {α : Type u}
    {parse : Std.Logical.ByteArray → ParseResult α}
    (stream : StreamingParser parse)
    {chunks : Vec Std.Logical.ByteArray} {input : Std.Logical.ByteArray}
    (chunking : Vec.IsChunking chunks input) :
    stream.finish (stream.feedAll chunks) = parse input := by
  rw [feedAll, stream.rechunk, chunking]

/-- The canonical buffering implementation. It retains logical bytes and calls
the finite parser only when `finish` is requested. -/
def buffered {α : Type u}
    (parse : Std.Logical.ByteArray → ParseResult α) : StreamingParser parse where
  State := Std.Logical.ByteArray
  initial := Vec.empty
  feed := Vec.append
  finish := parse
  rechunk := by
    intro chunks
    congr 1
    induction chunks using Vec.recOnPush with
    | empty => rfl
    | push previous chunk inductionHypothesis =>
        simp [inductionHypothesis]
        rfl

end StreamingParser

/-- A streaming realization packages the precious finite classification proof
with a chunk-invariant implementation of that exact parser. -/
structure StreamingRealizes {α : Type} {format : Format α}
    (semantics : FormatSemantics format)
    (parse : Std.Logical.ByteArray → ParseResult α) : Prop where
  parser : ParserRealizes semantics parse
  streaming : Nonempty (StreamingParser parse)

/-- Every realized finite parser has the canonical buffering streaming
implementation; optimized streamers may later replace it behind the same law. -/
theorem ParserRealizes.bufferedStreaming {α : Type} {format : Format α}
    {semantics : FormatSemantics format}
    {parse : Std.Logical.ByteArray → ParseResult α}
    (parser : ParserRealizes semantics parse) :
    StreamingRealizes semantics parse :=
  ⟨parser, ⟨StreamingParser.buffered parse⟩⟩

end Grass.Grammar
