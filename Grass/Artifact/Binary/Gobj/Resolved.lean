import Grass.Artifact.Binary.Gobj.ValidatedPayload

/-!
# Exact `.gobj` payload resolution

`ResolvedGobj` is indexed by the payload expected by an in-kernel owner. A
successful structural parse, filename, or digest alone cannot construct it;
`resolveGobj` checks exact payload equality and retains that parser equation.
-/

namespace Grass.Artifact.Binary.Gobj

open Grass.Grammar Grass.Std.Logical

/-- Untrusted bytes resolved to one exact expected first-order payload. -/
structure ResolvedGobj (expected : GobjPayload) where
  bytes : Std.Logical.ByteArray
  parsed : parseGobj bytes = .ok expected
deriving DecidableEq, Repr

/-- `resolveGobj` resolves bytes only when their payload is exactly expected. -/
def resolveGobj (expected : GobjPayload) (bytes : Std.Logical.ByteArray) :
    Except ParseError (ResolvedGobj expected) :=
  match parsed : parseGobj bytes with
  | .error error => .error error
  | .ok actual =>
    if exact : actual = expected then
      .ok {
        bytes := bytes
        parsed := parsed.trans (congrArg Except.ok exact) }
    else
      .error (.malformed ".gobj payload does not match expected object")

/-- Canonical serialization resolves to the payload that produced it. -/
@[simp] theorem resolveGobj_write (payload : GobjPayload) :
    resolveGobj payload (writeGobj payload) =
      .ok { bytes := writeGobj payload, parsed := parseGobj_write payload } := by
  unfold resolveGobj
  split
  case h_1 error observed =>
    rw [parseGobj_write] at observed
    contradiction
  case h_2 actual observed =>
    have actualEq : actual = payload := by
      rw [parseGobj_write] at observed
      exact Except.ok.inj observed.symm
    subst actual
    rw [dif_pos rfl]

/-- `ResolvedGobj.parseExact` exposes the exact expected parse equation. -/
theorem ResolvedGobj.parseExact {expected : GobjPayload}
    (resolved : ResolvedGobj expected) :
    parseGobj resolved.bytes = .ok expected :=
  resolved.parsed

/-- Parsed but unequal payloads are rejected by exact resolution. -/
theorem resolveGobj_mismatch {expected actual : GobjPayload}
    {bytes : Std.Logical.ByteArray}
    (parsed : parseGobj bytes = .ok actual) (different : actual ≠ expected) :
    resolveGobj expected bytes =
      .error (.malformed ".gobj payload does not match expected object") := by
  unfold resolveGobj
  split
  case h_1 error observed =>
    rw [observed] at parsed
    contradiction
  case h_2 found observed =>
    have foundEq : found = actual := by
      rw [observed] at parsed
      exact Except.ok.inj parsed
    subst found
    rw [dif_neg different]

end Grass.Artifact.Binary.Gobj
