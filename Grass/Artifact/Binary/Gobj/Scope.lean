import Grass.Artifact.Binary.Gobj.Framing
import Grass.Artifact.Binary.Unary
import Grass.Core.Identifiers
import Grass.Std.Logical.Text

/-!
# Canonical `.gobj` stable-scope encoding

Stable scopes are nominal pairs of strings, not hashes or fixed-width handles.
Each UTF-8 component is framed by a total unary length: one `1` byte per
payload byte followed by a `0` terminator.  The deliberately simple framing is
unbounded over logical `Nat`, canonical, and keeps component boundaries
unambiguous without narrowing the open-world `StableId` type.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Artifact.Binary Grass.Grammar Grass.Std.Logical

/-- Stable scope identity is the foundation's structured nominal identifier. -/
abbrev StableScopeId := Grass.StableId

/-- Canonical serialization of one UTF-8 string component. -/
def writeScopeComponent (value : String) : Std.Logical.ByteArray :=
  writeUnaryNat (Text.utf8 value).length ++ Text.utf8 value

/-- Independent language for one canonical UTF-8 scope component, pairing its
unary byte length with exactly those encoded bytes. -/
def scopeComponentFormat : Format String :=
  .lift
    (.seq unaryNatFormat fun count => repeatedBytesFormat count)
    fun value => ((Text.utf8 value).length, Text.utf8 value)

/-- `derives_scopeComponent_iff` characterizes component derivations by the
canonical writer bytes and an arbitrary retained suffix. -/
theorem derives_scopeComponent_iff {input rest : Std.Logical.ByteArray}
    {value : String} :
    Derives scopeComponentFormat input value rest ↔
      input = writeScopeComponent value ++ rest := by
  constructor
  · intro derivation
    have sequence := derivation.lift_inner
    rcases sequence.seqOuterShape with
      ⟨middle, count, bytes, pairEq, lengthDerivation, bytesDerivation⟩
    injection pairEq with countValue bytesValue
    subst count
    subst bytes
    have lengthInput := derives_unaryNatFormat_iff.mp lengthDerivation
    have bytesInput := (derives_repeatedBytes_iff.mp bytesDerivation).1
    rw [lengthInput, bytesInput]
    simp [writeScopeComponent, writeUnaryNat, Vec.append_assoc]
  · intro equality
    rw [equality]
    apply Derives.lift
    exact Derives.seq
      (by simpa [writeScopeComponent, writeUnaryNat, Vec.append_assoc] using
        unaryNat_derives (Text.utf8 value).length (Text.utf8 value ++ rest))
      (by simpa using anyBytes_derives (Text.utf8 value) rest)

/-- A component carries its bytes once plus an equally long unary prefix. -/
@[simp] theorem length_writeScopeComponent (value : String) :
    (writeScopeComponent value).length = 2 * (Text.utf8 value).length + 1 := by
  simp [writeScopeComponent]
  omega

/-- Parse one canonical UTF-8 string component. -/
def readScopeComponent (input : Std.Logical.ByteArray) : ParseResult String :=
  match readUnaryNat input with
  | .done count afterLength =>
      match takeExact count afterLength with
      | .done bytes suffix =>
          match Text.decode? bytes with
          | some value => .done value suffix
          | none => .invalid (.malformed "invalid UTF-8 in .gobj scope")
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
  | .needMore _ => .needMore (some (input.length + 1))
  | .invalid error => .invalid error

/-- `readScopeComponent_write_append` proves canonical component recovery with
every suffix preserved. -/
@[simp] theorem readScopeComponent_write_append (value : String)
    (suffix : Std.Logical.ByteArray) :
    readScopeComponent (writeScopeComponent value ++ suffix) =
      .done value suffix := by
  unfold readScopeComponent writeScopeComponent
  rw [Vec.append_assoc, readUnaryNat_write_append]
  simp only
  rw [takeExact_append (by rfl)]
  simp [Text.decode?_utf8]

/-- Arbitrary successful component parsing is equivalent to the independent
component format derivation. -/
theorem readScopeComponent_done_iff (input : Std.Logical.ByteArray)
    (value : String) (rest : Std.Logical.ByteArray) :
    readScopeComponent input = .done value rest ↔
      Derives scopeComponentFormat input value rest := by
  rw [derives_scopeComponent_iff]
  constructor
  · intro parsed
    unfold readScopeComponent at parsed
    split at parsed
    next count afterLength lengthParsed =>
      split at parsed
      next bytes suffix bytesParsed =>
        split at parsed
        next decodedValue decoded =>
          injection parsed with valueEq restEq
          subst value
          subst rest
          have lengthInput := derives_unaryNatFormat_iff.mp
            ((readUnaryNat_done_iff input count afterLength).mp lengthParsed)
          have bytesParts := takeExact_done bytesParsed
          have encoded : Text.utf8 decodedValue = bytes := by
            unfold Text.decode? at decoded
            split at decoded
            next valid =>
              injection decoded with decodedEq
              subst decodedValue
              exact Text.utf8_decode bytes valid
            next => contradiction
          have countEq : count = (Text.utf8 decodedValue).length := by
            calc
              count = bytes.length := bytesParts.1.symm
              _ = (Text.utf8 decodedValue).length :=
                congrArg Vec.length encoded.symm
          calc
            input = writeUnaryNat count ++ afterLength := by
              simpa [writeUnaryNat] using lengthInput
            _ = writeUnaryNat count ++ (bytes ++ suffix) := by
              rw [bytesParts.2]
            _ = writeScopeComponent decodedValue ++ suffix := by
              rw [← encoded, countEq]
              simp [writeScopeComponent, Vec.append_assoc]
        next => contradiction
      next => contradiction
      next => contradiction
    next => contradiction
    next => contradiction
  · intro canonical
    rw [canonical]
    exact readScopeComponent_write_append value rest

/-- Serialize both structural components; dotted display rendering is absent. -/
def writeStableScopeId (scope : StableScopeId) : Std.Logical.ByteArray :=
  writeScopeComponent scope.owner ++ writeScopeComponent scope.localName

/-- Independent language for the two nominal components of a stable scope. -/
def stableScopeIdFormat : Format StableScopeId :=
  .lift (.seq scopeComponentFormat fun _ : String => scopeComponentFormat)
    fun scope => (scope.owner, scope.localName)

/-- `derives_stableScopeId_iff` characterizes a scope derivation by its two
canonical component encodings and retained suffix. -/
theorem derives_stableScopeId_iff {input rest : Std.Logical.ByteArray}
    {scope : StableScopeId} :
    Derives stableScopeIdFormat input scope rest ↔
      input = writeStableScopeId scope ++ rest := by
  constructor
  · intro derivation
    have sequence := derivation.lift_inner
    rcases sequence.seqOuterShape with
      ⟨middle, owner, localName, pairEq, ownerDerivation, localDerivation⟩
    injection pairEq with ownerValue localValue
    subst owner
    subst localName
    have ownerInput := derives_scopeComponent_iff.mp ownerDerivation
    have localInput := derives_scopeComponent_iff.mp localDerivation
    rw [ownerInput, localInput]
    simp [writeStableScopeId, Vec.append_assoc]
  · intro equality
    subst input
    have ownerDerivation : Derives scopeComponentFormat
        (writeScopeComponent scope.owner ++
          (writeScopeComponent scope.localName ++ rest))
        scope.owner (writeScopeComponent scope.localName ++ rest) :=
      derives_scopeComponent_iff.mpr rfl
    have localDerivation : Derives scopeComponentFormat
        (writeScopeComponent scope.localName ++ rest) scope.localName rest :=
      derives_scopeComponent_iff.mpr rfl
    have pairDerivation :=
      Derives.seq (next := fun _ : String => scopeComponentFormat)
        ownerDerivation localDerivation
    change Derives
      (.lift (.seq scopeComponentFormat fun _ : String => scopeComponentFormat)
        fun scope : StableScopeId => (scope.owner, scope.localName))
      (writeStableScopeId scope ++ rest) scope rest
    rw [show writeStableScopeId scope ++ rest =
      writeScopeComponent scope.owner ++
        (writeScopeComponent scope.localName ++ rest) by
      simp [writeStableScopeId, Vec.append_assoc]]
    exact Derives.lift (value := scope) pairDerivation

/-- Scope width is derived from its two structured UTF-8 components. -/
@[simp] theorem length_writeStableScopeId (scope : StableScopeId) :
    (writeStableScopeId scope).length =
      2 * (Text.utf8 scope.owner).length +
        2 * (Text.utf8 scope.localName).length + 2 := by
  simp [writeStableScopeId]
  omega

/-- Parse both structured components of a stable scope. -/
def readStableScopeId (input : Std.Logical.ByteArray) : ParseResult StableScopeId :=
  match readScopeComponent input with
  | .done owner afterOwner =>
      match readScopeComponent afterOwner with
      | .done localName suffix => .done { owner, localName } suffix
      | .needMore hint => .needMore hint
      | .invalid error => .invalid error
  | .needMore hint => requireAfter 1 (.needMore hint)
  | .invalid error => .invalid error

/-- Structured scope serialization is injective through exact parser recovery. -/
@[simp] theorem readStableScopeId_write_append (scope : StableScopeId)
    (suffix : Std.Logical.ByteArray) :
    readStableScopeId (writeStableScopeId scope ++ suffix) =
      .done scope suffix := by
  unfold readStableScopeId writeStableScopeId
  rw [Vec.append_assoc, readScopeComponent_write_append]
  simp only
  rw [readScopeComponent_write_append]

/-- Complete canonical scope bytes are the empty-suffix prefix law. -/
@[simp] theorem readStableScopeId_write (scope : StableScopeId) :
    readStableScopeId (writeStableScopeId scope) = .done scope Vec.empty := by
  simpa using readStableScopeId_write_append scope Vec.empty

/-- Arbitrary successful stable-scope parsing is equivalent to the independent
two-component format derivation. -/
theorem readStableScopeId_done_iff (input : Std.Logical.ByteArray)
    (scope : StableScopeId) (rest : Std.Logical.ByteArray) :
    readStableScopeId input = .done scope rest ↔
      Derives stableScopeIdFormat input scope rest := by
  rw [derives_stableScopeId_iff]
  constructor
  · intro parsed
    unfold readStableScopeId at parsed
    split at parsed
    next owner afterOwner ownerParsed =>
      split at parsed
      next localName suffix localParsed =>
        injection parsed with scopeEq restEq
        subst scope
        subst rest
        have ownerInput := derives_scopeComponent_iff.mp
          ((readScopeComponent_done_iff input owner afterOwner).mp ownerParsed)
        have localInput := derives_scopeComponent_iff.mp
          ((readScopeComponent_done_iff afterOwner localName suffix).mp localParsed)
        rw [ownerInput, localInput]
        simp [writeStableScopeId, Vec.append_assoc]
      next => contradiction
      next => contradiction
    next _ hint _ =>
      have impossible : requireAfter (α := StableScopeId) 1 (.needMore hint) ≠
          .done scope rest := by
        cases hint <;> simp [requireAfter]
      exact (impossible parsed).elim
    next => contradiction
  · intro canonical
    rw [canonical]
    exact readStableScopeId_write_append scope rest

/-- No digest, registry handle, or display rendering mediates scope identity. -/
theorem writeStableScopeId_injective : Function.Injective writeStableScopeId := by
  intro left right equal
  have parsed := congrArg readStableScopeId equal
  simpa using parsed

/-- `readStableScopeId_classifies` exposes the total three-way parser result
for every untrusted input. -/
theorem readStableScopeId_classifies (input : Std.Logical.ByteArray) :
    (∃ scope suffix, readStableScopeId input = .done scope suffix) ∨
    (∃ hint, readStableScopeId input = .needMore hint) ∨
    (∃ error, readStableScopeId input = .invalid error) := by
  cases observed : readStableScopeId input with
  | done scope suffix => exact Or.inl ⟨scope, suffix, rfl⟩
  | needMore hint => exact Or.inr (Or.inl ⟨hint, rfl⟩)
  | invalid error => exact Or.inr (Or.inr ⟨error, rfl⟩)

end Grass.Artifact.Binary.Gobj
