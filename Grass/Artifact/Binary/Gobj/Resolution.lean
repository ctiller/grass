import Grass.Artifact.Binary.Gobj.Schema
import Grass.Grammar.Core

/-!
# Exact `.gobj` resolution

`ResolvedGobj` retains the parser equality to a checked payload already bound
to a construction certificate. `resolveGobj?` constructs that bridge only from
exact value equality and an empty parser suffix.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Construct.Link Grass.Grammar Grass.Std.Logical

universe u v w x

/-- A byte buffer parsed as the exact checked payload bound to one construction
certificate, consuming the complete file. -/
structure ResolvedGobj
    {Source : Type x} {RelocKind : Type u} {ImportIdentity : Type v}
    {SourceProvenance : Type w}
    {Exact : Source → RelocatableFragment RelocKind ImportIdentity SourceProvenance → Prop}
    {source : Source}
    {fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance}
    (certificate : CertifiedRelocatableFragment Exact source fragment)
    (parse : Std.Logical.ByteArray →
      ParseResult (GobjPayload RelocKind ImportIdentity SourceProvenance)) where
  binding : CertifiedGobjPayload certificate
  bytes : Std.Logical.ByteArray
  parsed : parse bytes = .done binding.payload Vec.empty

/-- Attempt exact resolution after untrusted parsing. Structural equality is
checked at the payload value; no digest or certificate name participates. -/
def resolveGobj?
    {Source : Type x} {RelocKind : Type u} {ImportIdentity : Type v}
    {SourceProvenance : Type w}
    [DecidableEq RelocKind] [DecidableEq ImportIdentity]
    [DecidableEq SourceProvenance]
    {Exact : Source → RelocatableFragment RelocKind ImportIdentity SourceProvenance → Prop}
    {source : Source}
    {fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance}
    {certificate : CertifiedRelocatableFragment Exact source fragment}
    (parse : Std.Logical.ByteArray →
      ParseResult (GobjPayload RelocKind ImportIdentity SourceProvenance))
    (binding : CertifiedGobjPayload certificate)
    (bytes : Std.Logical.ByteArray) : Option (ResolvedGobj certificate parse) :=
  if parsed : parse bytes = .done binding.payload Vec.empty then
    some {
      binding := binding
      bytes := bytes
      parsed := parsed
    }
  else
    none

/-- Exact resolution succeeds precisely when parsing returns the bound payload
and consumes the complete byte buffer. -/
theorem resolveGobj?_isSome_iff
    {Source : Type x} {RelocKind : Type u} {ImportIdentity : Type v}
    {SourceProvenance : Type w}
    [DecidableEq RelocKind] [DecidableEq ImportIdentity]
    [DecidableEq SourceProvenance]
    {Exact : Source → RelocatableFragment RelocKind ImportIdentity SourceProvenance → Prop}
    {source : Source}
    {fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance}
    {certificate : CertifiedRelocatableFragment Exact source fragment}
    (parse : Std.Logical.ByteArray →
      ParseResult (GobjPayload RelocKind ImportIdentity SourceProvenance))
    (binding : CertifiedGobjPayload certificate)
    (bytes : Std.Logical.ByteArray) :
    (resolveGobj? parse binding bytes).isSome = true ↔
      parse bytes = .done binding.payload Vec.empty := by
  by_cases parsed : parse bytes = .done binding.payload Vec.empty
  · simp [resolveGobj?, parsed]
  · simp [resolveGobj?, parsed]

/-- A resolved file's payload names exactly the fragment retained by its
construction certificate. -/
theorem ResolvedGobj.fragment_exact
    {Source : Type x} {RelocKind : Type u} {ImportIdentity : Type v}
    {SourceProvenance : Type w}
    {Exact : Source → RelocatableFragment RelocKind ImportIdentity SourceProvenance → Prop}
    {source : Source}
    {fragment : RelocatableFragment RelocKind ImportIdentity SourceProvenance}
    {certificate : CertifiedRelocatableFragment Exact source fragment}
    {parse : Std.Logical.ByteArray →
      ParseResult (GobjPayload RelocKind ImportIdentity SourceProvenance)}
    (resolved : ResolvedGobj certificate parse) :
    resolved.binding.payload.fragment = fragment :=
  resolved.binding.fragmentExact

end Grass.Artifact.Binary.Gobj
