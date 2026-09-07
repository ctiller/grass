import Grass.Construct.Link.Raw

/-!
# Verified-object payload schema

`GobjPayload` is the proof-free serialization view of construction's
format-neutral `RelocatableFragment`. `checkGobjPayload` validates the current
format version and delegates structural validity to the producer-owned
`RelocatableFragment.WellFormed` predicate. `CertifiedGobjPayload` is the
in-kernel equality bridge to an exact construction certificate.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Construct.Link

universe u v w x

/-- The only `.gobj` format version currently accepted for writing or linking. -/
def currentFormatVersion : Nat := 1

/-- Proof-free `.gobj` content. Relocation, import, and provenance vocabularies
remain parameters owned by their producing ISA/ABI, platform, and source facets. -/
structure GobjPayload (RelocKind : Type u) (ImportIdentity : Type v)
    (SourceProvenance : Type w) where
  formatVersion : Nat
  fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance
deriving Repr, DecidableEq

namespace GobjPayload

variable {RelocKind : Type u} {ImportIdentity : Type v} {SourceProvenance : Type w}

/-- The canonical payload corresponding to one producer fragment. -/
def current
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    GobjPayload RelocKind ImportIdentity SourceProvenance :=
  ⟨currentFormatVersion, fragment⟩

/-- A payload is writable only at the current version and with a structurally
valid producer fragment. -/
def WellFormed
    (payload : GobjPayload RelocKind ImportIdentity SourceProvenance) : Prop :=
  payload.formatVersion = currentFormatVersion ∧ payload.fragment.WellFormed

instance (payload : GobjPayload RelocKind ImportIdentity SourceProvenance) :
    Decidable payload.WellFormed := by
  unfold WellFormed
  infer_instance

/-- A current payload is well formed exactly when its raw fragment is. -/
@[simp] theorem current_wellFormed_iff
    (fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance) :
    (current fragment).WellFormed ↔ fragment.WellFormed := by
  simp [current, WellFormed]

end GobjPayload

/-- Checked writable payload. The proof is retained in memory and is not a
field of `GobjPayload` or part of its eventual byte representation. -/
structure CheckedGobjPayload {RelocKind : Type u} {ImportIdentity : Type v}
    {SourceProvenance : Type w}
    (payload : GobjPayload RelocKind ImportIdentity SourceProvenance) :
    Type (max u v w) where
  valid : payload.WellFormed

/-- Precise structural rejection before byte writing or verified linking. -/
inductive GobjValidationError where
  | unsupportedVersion (actual : Nat)
  | malformedFragment (fragment : LinkFragmentId)
deriving Repr, DecidableEq

/-- Validate version and construction-owned fragment structure without
manufacturing source-to-bytes authority. -/
def checkGobjPayload {RelocKind : Type u} {ImportIdentity : Type v}
    {SourceProvenance : Type w}
    (payload : GobjPayload RelocKind ImportIdentity SourceProvenance) :
    Except GobjValidationError (CheckedGobjPayload payload) :=
  if version : payload.formatVersion = currentFormatVersion then
    if valid : payload.fragment.WellFormed then
      .ok ⟨version, valid⟩
    else
      .error (.malformedFragment payload.fragment.id)
  else
    .error (.unsupportedVersion payload.formatVersion)

/-- Validation succeeds exactly for `GobjPayload.WellFormed`. -/
theorem checkGobjPayload_isOk_iff {RelocKind : Type u} {ImportIdentity : Type v}
    {SourceProvenance : Type w}
    (payload : GobjPayload RelocKind ImportIdentity SourceProvenance) :
    (checkGobjPayload payload).isOk = true ↔ payload.WellFormed := by
  by_cases version : payload.formatVersion = currentFormatVersion
  · by_cases valid : payload.fragment.WellFormed
    · simp [checkGobjPayload, GobjPayload.WellFormed, version, valid]
      rfl
    · simp [checkGobjPayload, GobjPayload.WellFormed, version, valid]
      rfl
  · simp [checkGobjPayload, GobjPayload.WellFormed, version]
    rfl

/-- Exact in-kernel binding between a `.gobj` payload and the fragment retained
by a construction certificate. Digest or identifier agreement cannot construct
the `fragmentExact` field. -/
structure CertifiedGobjPayload
    {Source : Type x} {RelocKind : Type u} {ImportIdentity : Type v}
    {SourceProvenance : Type w}
    {Exact : Source → RelocatableFragment RelocKind ImportIdentity SourceProvenance → Prop}
    {source : Source}
    {fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance}
    (certificate : CertifiedRelocatableFragment Exact source fragment) where
  payload : GobjPayload RelocKind ImportIdentity SourceProvenance
  checked : CheckedGobjPayload payload
  fragmentExact : payload.fragment = fragment

/-- The canonical current payload of a construction certificate is bound by
reflexive fragment equality and the certificate's retained structural check. -/
def CertifiedGobjPayload.current
    {Source : Type x} {RelocKind : Type u} {ImportIdentity : Type v}
    {SourceProvenance : Type w}
    {Exact : Source → RelocatableFragment RelocKind ImportIdentity SourceProvenance → Prop}
    {source : Source}
    {fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance}
    (certificate : CertifiedRelocatableFragment Exact source fragment) :
    CertifiedGobjPayload certificate where
  payload := .current fragment
  checked := ⟨by
    exact (GobjPayload.current_wellFormed_iff fragment).2 certificate.checked.valid⟩
  fragmentExact := rfl

end Grass.Artifact.Binary.Gobj
