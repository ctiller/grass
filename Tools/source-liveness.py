#!/usr/bin/env python3
"""Check each source document's recorded retrieval status against the network.

`Grass.Cite.SourceDocument.livenessProbe` has existed since this corpus began
and had no reader. Nothing in `Tools/`, `Tests/` or `.github/` looked at it, so
`SourceDocument.retrieval` was a status an author typed -- and
`Citation.FullyChecked`, which gates `CommonBasis.agreed` and
`JustifiedCostModel.citationsChecked`, rested on it. Two reviewers arrived at
that from opposite directions: one showed a docstring claiming the status was
"set by probing" was simply false, and one invented a `SourceDocument` carrying
`.verified` and rebuilt an attack the field was added to stop.

This is the reader. It fetches each `url` and asks whether `livenessProbe`
appears in what comes back, then compares that against the recorded status.

Why a probe string rather than an HTTP status: `Grass/ISA/X86/Citation.lean`
records three measured ways status codes lie about exactly these two publishers.
`intel.com` returns 403 to an automated request while serving the manual to a
browser. AMD's recorded URL returns 200 with a client-routed shell identical for
every path on the host. And `amd.com` serves a byte-identical response for every
document number under both of its document trees -- so a content-length check,
and even a checksum-stability check, pass uniformly as well. Only asserting on
the document's own text separates these cases.

What this cannot establish: that the document served is the *revision* the
citations were written against. The probe is a title fragment, so a publisher
replacing revision 092 with 093 at the same URL passes it. `Citation.confirmed`
still records a human following an anchor and remains unmechanised. This closes
the narrower question of whether the recorded retrieval status is true today.

Usage:
    lake env lean --run Tests/Emit.lean sources > sources.txt
    python Tools/source-liveness.py sources.txt

Exit status is 1 when a recorded status disagrees with what the network says.
A recorded `verified` whose probe is absent is the serious direction: the corpus
claims a checkable source and does not have one. A recorded `dead` whose probe
is present is also reported, because a document that came back is no longer a
release blocker and the ledger should stop saying it is.

This needs the network, so it is not a hermetic build gate.
`docs/VALIDATION.md` section 7 separates scheduled campaigns from the
per-commit suite, and this belongs with the physical probes rather than with the
differentials. A network failure is reported as `unreachable` and is not
silently treated as a dead source: "the check could not run" and "the document
is gone" are different findings, and conflating them is how a corpus acquires a
false release blocker.
"""

import sys
import urllib.error
import urllib.request
from pathlib import Path

TIMEOUT_SECONDS = 60

# The corpus is generated from `Vendor`, which is a closed inductive with two
# constructors, so this is the whole of it. A row count guards against the
# generator being narrowed the way a reviewer narrowed the NASM corpus.
EXPECTED_ROWS = 2

# A browser user agent, which helps with some publishers and not with these two:
# `intel.com` answers 403 to `urllib` and to `curl` alike, with this agent and a
# full `Accept` header set. It is presented anyway because it costs nothing and
# a future re-pin may land on a host that honours it. What actually separates
# bot policy from a dead document here is the refusal handling in `fetch`, not
# this string.
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)


def fetch(url: str) -> tuple[str, str, str]:
    """Return (text, refusal, error). At most one of the last two is non-empty.

    Three outcomes, not two, because this publisher set demands it.

    A `refusal` is the publisher declining to serve an automated client at all.
    `intel.com` answers 403 with a 464-byte page to `urllib` and to `curl`
    alike, with a browser user agent and a full `Accept` header set -- it serves
    the manual to a real browser and not to this. That is a statement about bot
    policy and *not* evidence about the document, which is exactly the trap
    `Grass.Cite.RetrievalStatus` was written around: "a status checker reports a
    live source dead". A first version of this tool fell into it and reported
    the Intel record as disagreeing.

    So a refusal is reported and never counted as death. The remediation is a
    browser, which is how the recorded status was established in the first
    place.
    """
    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(request, timeout=TIMEOUT_SECONDS) as response:
            raw = response.read()
    except urllib.error.HTTPError as exc:
        try:
            body = exc.read().decode("utf-8", "replace")
        except Exception:
            body = ""
        # A refusal that nonetheless contains the document's title is still a
        # live document, so the body is examined before the status is trusted.
        return body, f"HTTP {exc.code} ({len(body)} bytes)", ""
    except Exception as exc:
        return "", "", f"{type(exc).__name__}: {exc}"
    return raw.decode("utf-8", "replace"), "", ""


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2

    rows = []
    for line in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        fields = line.rstrip("\r").split("\t")
        if len(fields) != 4:
            print(f"malformed corpus row: {line!r}", file=sys.stderr)
            return 1
        rows.append(tuple(fields))

    if len(rows) < EXPECTED_ROWS:
        print(
            f"corpus has {len(rows)} rows, fewer than the {EXPECTED_ROWS} this "
            "tool was reviewed against. Coverage may only grow; if the "
            "reduction is deliberate, lower EXPECTED_ROWS in the same reviewed "
            "edit that shrinks the corpus.",
            file=sys.stderr)
        return 1

    disagreements = []
    unreachable = []
    refused = []
    agreed = []
    for doc_id, status, probe, url in rows:
        text, refusal, error = fetch(url)
        if error:
            unreachable.append((doc_id, url, error))
            continue
        present = probe in text
        if refusal and not present:
            # The publisher declined to serve a robot. That says nothing about
            # whether the document is there; see `fetch`.
            refused.append((doc_id, url, refusal, status))
            continue
        if status == "verified" and not present:
            disagreements.append(
                (doc_id, url,
                 f"recorded verified, but {probe!r} is absent from "
                 f"{len(text)} bytes served"))
        elif status == "dead" and present:
            disagreements.append(
                (doc_id, url,
                 f"recorded dead, but {probe!r} is present in what the "
                 "location serves; it may have come back"))
        else:
            agreed.append((doc_id, status, present))

    for doc_id, url, note in disagreements:
        print(f"DISAGREES  {doc_id}", file=sys.stderr)
        print(f"    url    {url}", file=sys.stderr)
        print(f"    {note}", file=sys.stderr)
    for doc_id, url, error in unreachable:
        print(f"UNREACHABLE  {doc_id}: {error}", file=sys.stderr)
        print(f"    url  {url}", file=sys.stderr)
        print("    Not counted as dead: a check that could not run and a "
              "document that is gone are different findings.", file=sys.stderr)
    for doc_id, url, refusal, status in refused:
        print(f"REFUSED  {doc_id}: {refusal}, recorded {status}")
        print(f"    url  {url}")
        print("    The publisher declined to serve an automated client. This "
              "is bot policy, not evidence about the document, and is not "
              "counted as death -- confirm in a browser.")

    if disagreements:
        print(
            f"source liveness: {len(rows)} documents, {len(disagreements)} "
            f"disagree with their recorded status, {len(unreachable)} "
            "unreachable", file=sys.stderr)
        return 1

    summary = ", ".join(
        f"{doc_id} {status} (probe {'found' if present else 'absent'})"
        for doc_id, status, present in agreed) or "none checkable"
    extra = ""
    if refused:
        extra += f"; {len(refused)} refused an automated client"
    if unreachable:
        extra += f"; {len(unreachable)} unreachable"
    print(f"source liveness: {len(rows)} documents, {len(agreed)} confirmed "
          f"against what the location serves -- {summary}{extra}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
