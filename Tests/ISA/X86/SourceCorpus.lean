import Grass.ISA.X86.Sources

/-!
# Source-retrieval corpus, for checking recorded liveness against the network

`Grass.Cite.SourceDocument.livenessProbe` has existed since this corpus began
and has never had a reader. Nothing in `Tools/`, `Tests/` or `.github/` ever
looked at it, so `SourceDocument.retrieval` was a status an author typed and
`Citation.FullyChecked` -- which gates `CommonBasis.agreed` and
`JustifiedCostModel.citationsChecked` -- rested on it. Two reviewers made the
same point from opposite directions: one that a docstring claiming the status is
"set by probing" was false, and one that an invented document carrying
`.verified` defeats the whole obligation.

This is the reader. `Tools/source-liveness.py` fetches each `url` and checks
whether `livenessProbe` appears in what comes back, then compares that against
the recorded `retrieval`. A recorded `.verified` whose probe string is absent is
a finding; so is a recorded `.dead` whose probe string is present, because a
document that came back is no longer a release blocker.

## Why a probe string and not an HTTP status

`Grass/ISA/X86/Citation.lean` records three ways status-code checking fails on
exactly these two publishers, all measured rather than supposed. `intel.com`
returns 403 to an automated request while serving the manual to a browser. AMD's
recorded URL returns 200 with a client-routed shell identical for every path.
And -- found on the 2026-09-03 re-check -- `amd.com` serves a byte-identical
response for every document number under both of its document trees, so a
content-length or checksum-stability check passes uniformly too.

Only asserting on the document's own text separates these, which is why the
probe is a string to look for rather than a code to compare.

## What this cannot establish

That the document at the URL is the *revision* the citations were written
against. The probe is a title fragment; a publisher who replaces revision 092
with 093 at the same URL passes it. `Citation.confirmed` still records a human
following an anchor, and that remains unmechanised. This closes the narrower
question of whether the recorded retrieval status is currently true.

It also needs the network, so it is not a hermetic build gate. `docs/VALIDATION.md`
section 7 separates scheduled campaigns from the per-commit suite for this
reason, and this belongs with the physical probes rather than with the
differentials.
-/

namespace Grass.Tests.ISA.X86.SourceC

open Grass.Cite Grass.ISA.X86

/-- The recorded retrieval status, as a word the tool can compare. -/
def statusWord : RetrievalStatus → String
  | .unverified => "unverified"
  | .verified _ => "verified"
  | .dead _ _ => "dead"

/-- A corpus row: one registered source document. -/
structure Row where
  /-- The document's identifier. -/
  id : String
  /-- The recorded retrieval status. -/
  status : String
  /-- The text that must appear in what the location serves. -/
  probe : String
  /-- Where the corpus says the document is. -/
  url : String

/-- Every document a citation in this profile can name.

Drawn from `Vendor.document` rather than listed, so a new vendor cannot acquire
a document that this check does not fetch. `Vendor` is a closed inductive, which
is what makes that exhaustive. -/
def corpus : List Row :=
  [Vendor.intel, Vendor.amd].filterMap fun v =>
    let d := v.document
    d.livenessProbe.map fun probe =>
      { id := d.id.text, status := statusWord d.retrieval
        probe := probe, url := d.url }

end Grass.Tests.ISA.X86.SourceC

/-- Print the corpus as tab-separated `id<TAB>status<TAB>probe<TAB>url` lines.

Top level rather than in the namespace because `lake env lean --run` looks for
`main` there. -/
def main : IO Unit := do
  for r in Grass.Tests.ISA.X86.SourceC.corpus do
    IO.println (r.id ++ "\t" ++ r.status ++ "\t" ++ r.probe ++ "\t" ++ r.url)
