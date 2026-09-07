import Grass.Unsafe.Control
import Grass.Unsafe.Import

/-!
# Checked raw import pipeline

`Decoder.importClosed` composes total byte decoding with
`ControlEvidence.close`.  Success returns one `ClosedImport`; failure retains
whether byte decoding or target closure failed, and no partial hierarchy is
returned through the result type.
-/

namespace Grass.Unsafe

universe u v w x y

/-- Typed failure of the combined decode and control-closure pipeline. -/
inductive CheckedImportError (DecodeError : Type w) (Target : Type x) (Site : Type y) where
  | decode (error : ImportError DecodeError)
  | control (error : ControlEvidenceError Target Site)
deriving Repr, DecidableEq

namespace Decoder

variable {Byte : Type v} {Instruction : Type u} {DecodeError : Type w}
  {Target : Type x} {Site : Type y}
  [DecidableEq Target] [DecidableEq Site]

/-- Decode every byte and close every imported control target, or return the
first typed failure without a usable partial hierarchy. -/
def importClosed (decoder : Decoder Byte Instruction DecodeError) (bytes : List Byte)
    (model : ControlModel Instruction Target Site)
    (evidenceFor : (raw : RawHierarchy Instruction) → ControlEvidence raw model) :
    Except (CheckedImportError DecodeError Target Site) (ClosedImport model) :=
  match decoder.importRaw bytes with
  | .error error => .error (.decode error)
  | .ok raw =>
      match (evidenceFor raw).close with
      | .error error => .error (.control error)
      | .ok closed => .ok closed

end Decoder

end Grass.Unsafe
