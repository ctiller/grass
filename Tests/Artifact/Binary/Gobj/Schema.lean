import Grass.Artifact.Binary.Gobj.Schema

/-! # `.gobj` schema and exact-certificate binding fixtures -/

namespace Grass.Tests.Artifact.Binary.Gobj.Schema

open Grass Grass.Artifact.Binary.Gobj Grass.Construct.Link Grass.Std.Logical

inductive RelocKind where | relative
deriving Repr, DecidableEq

inductive ImportIdentity where | consoleWrite
deriving Repr, DecidableEq

inductive Provenance where | authored
deriving Repr, DecidableEq

def stable (name : String) : StableId := ⟨"fixture", name⟩

def fragmentId : LinkFragmentId := ⟨stable "fragment"⟩

def validFragment : RelocatableFragment RelocKind ImportIdentity Provenance where
  id := fragmentId
  sections := []
  definitions := []
  relocations := []
  externals := []
  entryCandidates := []
  sourceMap := []

example : validFragment.WellFormed := by
  decide

example : (checkGobjPayload (.current validFragment)).isOk = true := by
  rw [checkGobjPayload_isOk_iff]
  decide

def unsupported : GobjPayload RelocKind ImportIdentity Provenance :=
  ⟨2, validFragment⟩

example : checkGobjPayload unsupported = .error (.unsupportedVersion 2) := by
  rfl

def Exact (_ : Unit)
    (fragment : RelocatableFragment RelocKind ImportIdentity Provenance) : Prop :=
  fragment = validFragment

def certificate : CertifiedRelocatableFragment Exact () validFragment where
  checked := ⟨by decide⟩
  exact := rfl

def bound : CertifiedGobjPayload certificate :=
  CertifiedGobjPayload.current certificate

example : bound.payload.fragment = validFragment := bound.fragmentExact

end Grass.Tests.Artifact.Binary.Gobj.Schema
