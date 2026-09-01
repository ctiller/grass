# Precious languages and replaceable parsers

This document owns Grass's typed language/format specification front. It is
normative for text grammars, binary formats, instruction decoders, container
formats, and token languages. It does not prescribe a parser implementation or
process topology.

## 1. Precious boundary

A language specification states:

- exactly which complete inputs are valid;
- the semantic value or transition denoted by every valid input;
- which finite inputs are valid prefixes needing more data;
- which inputs are irrecoverably invalid, including the error classification
  when that classification is observable;
- whether multiple derivations are forbidden, retained, or resolved by an
  explicit semantic rule; and
- canonical writer policy only when exact serialization is itself promised.

Buffering, allocation, table generation, lexer/parser splitting, backtracking,
memoization, SIMD scanning, process decomposition, error-message wording, and
recovery policy are non-precious unless the product contract observes them.

## 2. Typed format algebra

The core is an inductive, typed description rather than an opaque parsing
function:

```lean
inductive Format : Type -> Type
  | pure (value : alpha)
  | byte (accepts : Byte -> Prop)
  | bits (width : Nat) (accepts : BitVec width -> Prop)
  | seq (left : Format alpha) (right : alpha -> Format beta)
  | choice (alternatives : FiniteNonempty (Format alpha))
  | repeat (count : Nat) (item : Format alpha)
  | lengthPrefixed (length : Format Nat)
      (body : (n : Nat) -> Format (SizedValue alpha n))
  | refine (inner : Format alpha) (accepts : alpha -> Prop)
  | iso (inner : Format alpha) (equiv : alpha <-> beta)
  | recursive (guard : ProductiveRecursionWitness) (body : Format alpha)

structure Derives (format : Format alpha) (input : ByteArray)
    (value : alpha) (rest : ByteArray) : Prop
```

The displayed constructors are the minimum design target, not a closed forever
list. Text sugar may resemble EBNF; typed combinators may resemble parser
libraries. Both elaborate to `Format`. Binary formats additionally need endian
integers, tagged unions, alignment/padding, bounded variable integers, checksums,
offset tables, and dependent lengths. Each is a derived constructor or a
reviewed extension with a denotational equation.

Ordered choice is not implicit. PEG-style priority changes meaning and is
precious when selected. Otherwise `choice` denotes the union of derivations and
the specification separately proves unambiguity or states an explicit
disambiguation relation. Parser implementation order may not choose meaning.

## 3. Streaming distinction

A finite byte buffer has three semantic outcomes:

```lean
inductive ParseResult (alpha : Type)
  | done (value : alpha) (rest : ByteArray)
  | needMore (minimumAdditional : Option Nat)
  | invalid (error : ParseError)
```

`needMore` means some extension can produce a derivation and the current input
contains no complete derivation selected by the format's consumption rule.
`invalid` means no extension can repair the rejected prefix. The parser may not
turn partial transport delivery into malformed syntax. This is the semantic
junction from partial reads to byte channels: rechunking changes neither
derivations nor the final classification.

Formats name their consumption rule. A whole-input language requires empty
`rest`; a prefix format returns the exact suffix; a framed stream repeatedly
consumes one nonempty prefix. Nullable repetition and unguarded recursion are
rejected because they can manufacture silent divergence.

## 4. Required parser and writer theorems

For a selected implementation parser:

```lean
structure ParserRealizes (format : Format alpha)
    (parse : ByteArray -> ParseResult alpha) where
  successSound : forall input value rest,
    parse input = .done value rest -> Derives format input value rest
  successComplete : forall input value rest,
    SelectedDerivation format input value rest ->
    parse input = .done value rest
  needMoreExact : forall input hint,
    parse input = .needMore hint <-> RepairableIncompletePrefix format input hint
  invalidExact : forall input error,
    parse input = .invalid error <-> IrrecoverablyInvalidPrefix format input error
  consumes : EverySuccessObeysConsumptionAndProgress format parse
```

This is stronger than “success implies valid.” It prevents a parser which
rejects every input, accepts only an easy subset, consumes the wrong suffix, or
misclassifies a split valid message as invalid.

A writer is a separate realization because a language can admit several
encodings for one value:

```lean
structure WriterRealizes (format : Format alpha)
    (write : alpha -> ByteArray) where
  sound : forall value, Derives format (write value) value ByteArray.empty
  canonical : SelectedWriterPolicy format write

theorem parse_write (parser : ParserRealizes format parse)
    (writer : WriterRealizes format write) (value : alpha) :
    parse (write value) = .done value ByteArray.empty := ...
```

Every Grass emitter has the corresponding reader and `parse_write` theorem.
Formats may additionally demand `write_parse`, canonical uniqueness, exact byte
identity, prefix preservation, executable loading, or semantic decoding. For
x86 and other noncanonical instruction encodings, the important theorem may be
that emitted bytes decode to the selected instruction semantics rather than
that decoding and re-encoding reproduces the same bytes.

## 5. Syntax versus contextual legality

Grammar derivation answers whether bytes have a syntactic form and value.
Protocol or machine state answers whether that value is legal now. These are
separate precious relations with an explicit connection:

```text
byte chunks
  -> Format derivation
  -> typed frame/instruction/token
  -> stateful transition relation
  -> observations, custody, resources, and obligations
```

For HTTP/2, `Format` owns the client preface, frame header, frame payload forms,
HPACK integers/strings/Huffman blocks, and exact invalid/incomplete prefixes.
The HTTP/2 protocol relation owns stream states, connection-local HPACK order,
CONTINUATION exclusion, flow-control credit, SETTINGS effects, error scope,
RST_STREAM, and GOAWAY. A parser process graph is one non-precious composition
of those relations.

The same split applies to PE/COFF structure versus loader policy, x86 bytes
versus enabled-feature/machine semantics, gzip members versus checksum/history
state, and source grammar versus name/type checking.

## 6. Proof economy and implementation freedom

`Format.parserRequirement format` is the standard way for a higher-level
precious process to demand “a process which implements this parser.” It exports
only the byte-input/result protocol and `ParserRealizes` theorem family. The
enclosing root `SpecProcess` is proved parametrically over every satisfying
witness; refinement later selects or constructs one and captures any internal
lexer/parser graph behind that boundary.

Standard combinators derive parser soundness/completeness compositionally.
Generated tables carry small checked certificates back to the originating
`Format`; table generation is not trusted. Authors provide semantic refinement
predicates, ambiguity decisions, unusual recursion/productivity arguments, and
stateful legality connections. Optimized scalar, SIMD, table-driven, generated,
parallel, and process-pipelined parsers may all realize the same format.

Assembly authors can implement a parser directly. A typed CFG block consumes a
proved input slice and parser state and returns `done`, `needMore`, or `invalid`
with exact residual custody. Local symbolic execution or a verified macro proves
that block refines one format operation. No parser DSL is required in the final
instruction stream.

## 7. Adversarial acceptance

Each format fixture includes empty input; every split of representative valid
encodings; trailing suffixes; truncated tags, lengths, fields, and escape/code
sequences; maximum and overflowing lengths; invalid reserved values; ambiguous
alternatives; nullable-recursion rejection; and mutations that accept one
forbidden input or reject one required input. Fuzzing compares independent
implementations and vendor/system behavior, but only forall proofs discharge
`ParserRealizes`.

The grammar front is successful only if changing parser organization or tuning
does not change the precious specification, while changing the accepted
language or semantic mapping does.
