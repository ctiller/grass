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
structure ParseDiagnostic where
  errorClass : ParseErrorClass
  details : DiagnosticData

inductive ParseResult (alpha : Type)
  | done (value : alpha) (rest : ByteArray)
  | needMore (minimumAdditional : Option Nat)
  | invalid (diagnostic : ParseDiagnostic)
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

### 3.1 Lawful selection and finite-prefix classification

`SelectedDerivation`, `RepairableIncompletePrefix`, and
`IrrecoverablyInvalidPrefix` are specification relations. They are not three
arbitrary predicates that an executable parser may define to describe its own
answers. Otherwise a parser which rejects every input could select no
derivations, call every input invalid, and satisfy a vacuous realization
contract.

A format therefore packages a reviewed selection/consumption policy and a
law-bearing finite-prefix semantics. Selection is constrained independently of
the parser: it may resolve ambiguity, but it may neither invent a derivation nor
discard every admissible derivation. The concrete representation may differ,
but it must expose the following facts:

```lean
structure ConsumptionPolicy (format : Format alpha) where
  rule : ConsumptionRule
  admits : ByteArray -> alpha -> ByteArray -> Prop
  admits_iff : forall input value rest,
    admits input value rest <->
      ConsumptionRuleAdmits rule input value rest

structure SelectionPolicy (format : Format alpha) where
  consumption : ConsumptionPolicy format
  selects : ByteArray -> alpha -> ByteArray -> Prop
  subset : forall input value rest,
    selects input value rest ->
      Derives format input value rest /\
      consumption.admits input value rest
  total : forall input,
    (exists value rest,
      Derives format input value rest /\
      consumption.admits input value rest) ->
    exists value rest, selects input value rest
  unique : forall input left leftRest right rightRest,
    selects input left leftRest -> selects input right rightRest ->
    left = right /\ leftRest = rightRest

structure FormatSemantics (format : Format alpha) where
  selection : SelectionPolicy format
  repairable : ByteArray -> Prop
  irrecoverable : ByteArray -> ParseErrorClass -> Prop

  repairable_iff : forall input, repairable input <->
    NoSelectedDerivation selection input /\
    SomeGenuineExtensionHasSelectedDerivation selection input
  irrecoverable_iff : irrecoverable input errorClass <->
    NoExtensionHasSelectedDerivation selection input /\
    ClassifiesInvalidPrefix input errorClass
  irrecoverable_unique : forall input left right,
    irrecoverable input left -> irrecoverable input right -> left = right
  classified : forall input,
    ExactlyOne
      (ExistsSelectedDerivation selection input)
      (repairable input)
      (exists errorClass, irrecoverable input errorClass)
  consumes : forall input value rest,
    selection.selects input value rest ->
    selection.consumption.admits input value rest
```

The policy supplies the semantic choice when the underlying grammar has
multiple derivations. It may select PEG priority, a canonical representation,
or another reviewed rule, but parser implementation order is not a policy.
Changing the parser does not change which derivations the policy selects. The
consumption policy is likewise tied by `admits_iff` to a named rule rather than
an arbitrary filter. Consequently `subset` plus `total` cannot be satisfied by
making either selection or consumption reject everything: whenever the named
rule admits any real derivation, exactly one such derivation is selected.

`SomeGenuineExtensionHasSelectedDerivation` requires a nonempty repairing
extension; appending bytes which remain wholly in `rest` is not progress. When
`minimumAdditional = some n`, `n` is the least positive extension length that
can reach a selected success. A parser which cannot compute or promise that
least value returns `none`; it may not publish a convenient lower bound under
the name “minimum.” The optional hint is deliberately not part of the
classification relation: two implementations may return `none` and the same
exact `some n` while realizing the same precious finite-prefix semantics.

Failure classes and diagnostics are separate. The ordinary realization
contract compares a stable `ParseErrorClass` such as `malformed`, `unsupported`,
`arithmeticOverflow`, or `trailingInput`. An implementation may attach source
locations, paths, excerpts, and free-form wording, but those diagnostics are
projected away before semantic comparison. A product may deliberately select a
richer observable error algebra; only then do those details become precious.

## 4. Required parser and writer theorems

For a selected implementation parser:

```lean
structure ParserRealizes (semantics : FormatSemantics format)
    (parse : ByteArray -> ParseResult alpha) where
  successSound : forall input value rest,
    parse input = .done value rest ->
      semantics.selection.selects input value rest
  successComplete : forall input value rest,
    semantics.selection.selects input value rest ->
    parse input = .done value rest
  needMoreExact : forall input,
    (exists hint, parse input = .needMore hint) <->
      semantics.repairable input
  needMoreHintExact : forall input n,
    parse input = .needMore (some n) ->
    n = LeastPositiveRepairingExtensionLength semantics.selection input
  invalidClassExact : forall input errorClass,
    (exists diagnostic,
      parse input = .invalid diagnostic /\
      diagnostic.errorClass = errorClass) <->
    semantics.irrecoverable input errorClass
```

This is stronger than “success implies valid.” It prevents a parser which
rejects every input, accepts only an easy subset, consumes the wrong suffix, or
misclassifies a split valid message as invalid.

Those claims depend on the laws of `FormatSemantics`; merely proving the four
equations above against parser-chosen predicates proves nothing. Acceptance
includes compiled negative fixtures attempting a reject-all parser, a parser
which accepts only one valid value, false `needMore`, and rejection of a prefix
which a later chunk repairs.

A writer is a separate realization because a language can admit several
encodings for one value:

```lean
structure WriterRealizes (semantics : FormatSemantics format)
    (write : alpha -> ByteArray) where
  sound : forall value,
    semantics.selection.selects (write value) value ByteArray.empty
  canonical : SelectedWriterPolicy semantics write

theorem parse_write (parser : ParserRealizes semantics parse)
    (writer : WriterRealizes semantics write) (value : alpha) :
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

`Format.parserRequirement semantics` is the standard way for a higher-level
precious process to demand “a process which implements this parser.” It exports
only the byte-input/result protocol and `ParserRealizes semantics` theorem
family. The
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
`ParserRealizes semantics`.

The grammar front is successful only if changing parser organization or tuning
does not change the precious specification, while changing the accepted
language or semantic mapping does.
