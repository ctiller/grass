import Grass.Assembly.RipRelative
import Grass.Assembly.SignedRel32
import Grass.Assembly.SourceSpliceDecode
import Grass.Assembly.X86ClosedEncoding

/-! Deterministic resolution of checked spliced source outputs. External symbol
addresses and lengths remain explicit checked inputs; this module establishes no
PE placement, static-object binding, memory execution, or instruction execution claim. -/
namespace Grass.Assembly.SourceResolve
open Grass.ISA.X86 Grass.Std.Logical

structure StaticSymbol where
  name : String
  address : Nat
  byteLength : Nat
deriving Repr, DecidableEq
structure ImportSymbol where
  name : String
  iatAddress : Nat
deriving Repr, DecidableEq
structure Symbols where
  private mk ::
  statics : List StaticSymbol
  imports : List ImportSymbol
  staticNamesUnique : (statics.map StaticSymbol.name).Nodup
  importNamesUnique : (imports.map ImportSymbol.name).Nodup

/-- Build an environment from populations whose name uniqueness is already proved. -/
def Symbols.checked (statics : List StaticSymbol) (imports : List ImportSymbol)
    (staticNamesUnique : (statics.map StaticSymbol.name).Nodup)
    (importNamesUnique : (imports.map ImportSymbol.name).Nodup) : Symbols :=
  ⟨statics, imports, staticNamesUnique, importNamesUnique⟩

def Symbols.mk? (statics : List StaticSymbol) (imports : List ImportSymbol) : Option Symbols :=
  if hs : (statics.map StaticSymbol.name).Nodup then
    if hi : (imports.map ImportSymbol.name).Nodup then some ⟨statics, imports, hs, hi⟩ else none
  else none

def static? (s : Symbols) (name : String) := s.statics.find? (·.name == name)
def import? (s : Symbols) (name : String) := s.imports.find? (·.name == name)
def sourceOffset (codeBase : Nat) (sizes : List Nat) (index : Nat) :=
  codeBase + ByteLayout.offset sizes index

inductive Detail
  | encoded
  | branch (kind : Rel32.Kind) (targetIndex : Nat) (resolved : SignedRel32.Resolved)
  | ripStatic (destination : Gpr) (name : String) (symbol : StaticSymbol) (resolved : RipRelative.Result)
  | ripImport (name : String) (symbol : ImportSymbol) (resolved : RipRelative.Result)
  | sizeOf32 (destination : Gpr) (name : String) (symbol : StaticSymbol)

def Detail.Valid (symbols : Symbols) (codeBase : Nat) (sizes : List Nat)
    (source : Nat) (template : SourceSplice.FinalTemplate)
    (encoding : InsnEncoding) : Detail → Prop
  | .encoded => template = .encoded encoding
  | .branch kind targetIndex resolved =>
      template = .branch kind targetIndex ∧
      targetIndex < sizes.length ∧
      resolved.targetOffset = sourceOffset codeBase sizes targetIndex ∧
      SignedRel32.resolve? source (Rel32.encodedSize kind) resolved.targetOffset = some resolved ∧
      encoding = Rel32.encode kind resolved.bits
  | .ripStatic destination name symbol resolved =>
      (∃ prototype, template = .ripAddress destination name prototype) ∧
      static? symbols name = some symbol ∧
      RipRelative.resolve? (.address destination) source symbol.address = some resolved ∧
      resolved.sourceOffset = source ∧ resolved.targetOffset = symbol.address ∧ encoding = resolved.encoding
  | .ripImport name symbol resolved =>
      (∃ prototype, template = .ripCall name prototype) ∧
      import? symbols name = some symbol ∧
      RipRelative.resolve? .indirectCall source symbol.iatAddress = some resolved ∧
      resolved.sourceOffset = source ∧ resolved.targetOffset = symbol.iatAddress ∧ encoding = resolved.encoding
  | .sizeOf32 destination name symbol => symbol.byteLength < 2^32 ∧
      (∃ prototype, template = .sizeOf32 destination name prototype) ∧
      static? symbols name = some symbol ∧
      X86ClosedEncoding.encode ⟨.mov, [.register ⟨destination, .w32⟩,
        .immediate symbol.byteLength]⟩ = some encoding
structure Output {frame : SourceFrame.Result} {rootOffset : Nat}
    (splice : SourceSplice.Result frame rootOffset) (symbols : Symbols) (codeBase : Nat) where
  private mk ::
  index : Nat
  origin : SourceSplice.FinalOutput frame rootOffset
  originAt : splice.outputs[index]? = some origin
  template : SourceSplice.FinalTemplate
  templateExact : template = origin.template frame.saved.savedItems.length splice.initialization.entries.length
  encoding : InsnEncoding
  detail : Detail
  detailExact : detail.Valid symbols codeBase splice.finalSizes
    (sourceOffset codeBase splice.finalSizes index) template encoding
  sizeExact : encoding.size = template.size
  encodingDecodes : ∀ rest : ByteSeq, decodeInsn (encoding.toBytes ++ rest) = .ok (encoding, rest)

private structure Candidate (symbols : Symbols) (codeBase : Nat) (sizes : List Nat)
    (source : Nat) (template : SourceSplice.FinalTemplate) where
  encoding : InsnEncoding
  detail : Detail
  valid : detail.Valid symbols codeBase sizes source template encoding
  decodes : ∀ rest : ByteSeq, decodeInsn (encoding.toBytes ++ rest) = .ok (encoding, rest)
private def resolveAt? {frame rootOffset} (splice : SourceSplice.Result frame rootOffset)
    (symbols : Symbols) (codeBase index : Nat) (bound : index < splice.outputs.length) :
    Option (Output splice symbols codeBase) := do
  let origin := splice.outputs[index]
  let template := origin.template frame.saved.savedItems.length splice.initialization.entries.length
  let source := sourceOffset codeBase splice.finalSizes index
  let pair : Candidate symbols codeBase splice.finalSizes source template ← match ht : template with
    | .encoded e =>
        some ⟨e, Detail.encoded, ht,
          SourceSpliceDecode.final_encoded_decodes splice origin (List.getElem_mem bound) e ht⟩
    | .branch kind targetIndex => do
        if targetBound : targetIndex < splice.finalSizes.length then
          let target := sourceOffset codeBase splice.finalSizes targetIndex
          match hr : SignedRel32.resolve? source (Rel32.encodedSize kind) target with
          | none => none
          | some resolved =>
            let e := Rel32.encode kind resolved.bits
            some ⟨e, Detail.branch kind targetIndex resolved, ⟨ht, targetBound,
              (SignedRel32.resolve?_inputs hr).2.2, by
                have inputs := SignedRel32.resolve?_inputs hr
                simpa [inputs.2.2] using hr, rfl⟩,
              Rel32.decode_encode kind resolved.bits⟩
        else none
    | .ripAddress destination name _ => do
        match hs : static? symbols name with
        | none => none
        | some symbol =>
          match hr : RipRelative.resolve? (.address destination) source symbol.address with
          | none => none
          | some resolved =>
            have exact := RipRelative.resolve?_exact hr
            some ⟨resolved.encoding, Detail.ripStatic destination name symbol resolved,
              ⟨⟨_, ht⟩, hs, hr, exact.2.1, exact.2.2, rfl⟩, resolved.encoding_decodes⟩
    | .ripCall name _ => do
        match hs : import? symbols name with
        | none => none
        | some symbol =>
          match hr : RipRelative.resolve? .indirectCall source symbol.iatAddress with
          | none => none
          | some resolved =>
            have exact := RipRelative.resolve?_exact hr
            some ⟨resolved.encoding, Detail.ripImport name symbol resolved,
              ⟨⟨_, ht⟩, hs, hr, exact.2.1, exact.2.2, rfl⟩, resolved.encoding_decodes⟩
    | .sizeOf32 destination name _ => do
        match hs : static? symbols name with
        | none => none
        | some symbol =>
          if hsmall : symbol.byteLength < 2^32 then
            match he : X86ClosedEncoding.encode ⟨.mov, [.register ⟨destination, .w32⟩,
                .immediate symbol.byteLength]⟩ with
            | none => none
            | some e => some ⟨e, Detail.sizeOf32 destination name symbol,
                ⟨hsmall, ⟨_, ht⟩, hs, he⟩,
                X86ClosedEncoding.encode_decodes he⟩
          else none
  if hs : pair.encoding.size = template.size then
    some ⟨index, origin, List.getElem?_eq_getElem bound, template, rfl,
      pair.encoding, pair.detail, pair.valid, hs, pair.decodes⟩
  else none

private def resolveIndices? {frame rootOffset} (splice : SourceSplice.Result frame rootOffset)
    (symbols : Symbols) (codeBase : Nat) : List Nat → Option (List (Output splice symbols codeBase))
  | [] => some []
  | index :: indices => do
      if bound : index < splice.outputs.length then
        pure ((← resolveAt? splice symbols codeBase index bound) ::
          (← resolveIndices? splice symbols codeBase indices))
      else none

structure Result (frame : SourceFrame.Result) (rootOffset : Nat) where
  private mk ::
  splice : SourceSplice.Result frame rootOffset
  symbols : Symbols
  codeBase : Nat
  outputs : List (Output splice symbols codeBase)
  outputsExact : resolveIndices? splice symbols codeBase (List.range splice.outputs.length) = some outputs
  indicesExact : outputs.map Output.index = List.range splice.outputs.length
  countExact : outputs.length = splice.outputs.length
  encodingSizesExact : outputs.map (fun output => output.encoding.size) = splice.finalSizes

def resolve? {frame rootOffset} (splice : SourceSplice.Result frame rootOffset)
    (symbols : Symbols) (codeBase : Nat) : Option (Result frame rootOffset) := do
  match h : resolveIndices? splice symbols codeBase (List.range splice.outputs.length) with
  | none => none
  | some outputs =>
    if hi : outputs.map Output.index = List.range splice.outputs.length then
      if hc : outputs.length = splice.outputs.length then
        if hs : outputs.map (fun output => output.encoding.size) = splice.finalSizes then
          some ⟨splice,symbols,codeBase,outputs,h,hi,hc,hs⟩
        else none
      else none
    else none

/-- Successful resolution retains the exact splice, symbol environment and RVA base. -/
theorem resolve?_inputs {frame rootOffset} {splice : SourceSplice.Result frame rootOffset}
    {symbols : Symbols} {codeBase : Nat} {result : Result frame rootOffset}
    (success : resolve? splice symbols codeBase = some result) :
    result.splice = splice ∧ result.symbols = symbols ∧ result.codeBase = codeBase := by
  unfold resolve? at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  cases success
  exact ⟨rfl, rfl, rfl⟩

def Result.encodings {frame rootOffset} (r : Result frame rootOffset) := r.outputs.map Output.encoding

theorem Output.origin_exact {frame rootOffset} {splice : SourceSplice.Result frame rootOffset}
    {symbols : Symbols} {codeBase : Nat} (o : Output splice symbols codeBase) :
    splice.outputs[o.index]? = some o.origin := o.originAt

theorem Output.source_position {frame rootOffset} {splice : SourceSplice.Result frame rootOffset}
    {symbols : Symbols} {codeBase : Nat} (o : Output splice symbols codeBase) :
    sourceOffset codeBase splice.finalSizes o.index = codeBase + ByteLayout.offset splice.finalSizes o.index := rfl

theorem Result.output_indices {frame rootOffset} (r : Result frame rootOffset) :
    r.outputs.map Output.index = List.range r.splice.outputs.length := r.indicesExact

theorem Result.output_count {frame rootOffset} (r : Result frame rootOffset) :
    r.outputs.length = r.splice.outputs.length := r.countExact

theorem Result.encoding_sizes {frame rootOffset} (r : Result frame rootOffset) :
    r.encodings.map (fun encoding => encoding.size) = r.splice.finalSizes := by
  simpa [Result.encodings, List.map_map, Function.comp_def] using r.encodingSizesExact

end Grass.Assembly.SourceResolve
