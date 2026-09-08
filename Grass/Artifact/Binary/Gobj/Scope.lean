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

/-- Serialize both structural components; dotted display rendering is absent. -/
def writeStableScopeId (scope : StableScopeId) : Std.Logical.ByteArray :=
  writeScopeComponent scope.owner ++ writeScopeComponent scope.localName

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
