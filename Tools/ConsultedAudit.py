#!/usr/bin/env python3
"""Report declared facts that nothing reads.

Six rounds of adversarial review on the memory layer found eight defects that had
already passed a merge review, and all but one had the same shape: the model
carries a fact and nothing consults it. `AuthorityProvider.violationClass` against
the vocabulary. `Substep.faults`. `Obligation.owner`, so any context could
discharge any duty. `AccessIntent.isDevice`, which section 7.5 makes load-bearing.
`MemoryOrder.IsPortable`, whose own docstring says a consumer that skips it is the
permissive fallback law 8 forbids.

Review found those one at a time and each repair exposed another, so rounds four,
five and six each found defects in the immediately preceding round's fixes. That
is not a process converging. A field with no reader is a syntactic property, and
this checks it directly rather than hoping the next reader notices.

What it does NOT do: decide whether a field *should* be read. Plenty of declared
data is legitimately inert -- a diagnostic label, a name carried for reporting.
The allowlist below is where that judgement goes, and every entry needs a reason.
An unlisted field with no reader fails the build, so the decision is made once and
recorded rather than rediscovered by a reviewer.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCES = sorted((ROOT / "Grass").rglob("*.lean"))

# A field is *read* by a projection `.name`, by pattern-matching `name := x` in a
# `with`-update or destructuring, or by `open`ed dot-notation. Construction sites
# (`name := value` inside a structure literal) are writes, not reads, and are the
# thing a decorative field has plenty of.
DECL = re.compile(r"^\s{2,}(?:private\s+)?([a-z][A-Za-z0-9_']*)\s*:\s*[^=]")
STRUCTURE = re.compile(r"^\s*(?:private\s+)?structure\s+([A-Za-z_][A-Za-z0-9_.']*)")
ENDBLOCK = re.compile(r"^\S|^\s*(?:deriving|/-)")

# Fields deliberately carried without a reader. Every entry states why, and the
# entry is the record that the decision was made.
# A structure whose fields are propositions bundles proof obligations. Not reading
# such a field is the normal case -- its purpose is that a constructor had to
# discharge it -- so these are skipped by structure rather than field.
PROOF_BUNDLES = ("WellFormed", "Recognized", "Laws", "Holds", "Admits")

ALLOWED = {
    # Diagnostic identity: carried so a report or rejection can name which one,
    # never dispatched on.
    "id",
    "name",
    "label",
    "origin",
    # Structural payloads consumed by pattern matching rather than projection,
    # which this tool cannot see.
    "recognized",
    "entries",
    "runs",
    "bytes",
    "start",
    "aliases",
    "substeps",
    # --- Carried without a reader, each recorded as owed in
    # --- docs/MEMORY_IMPLEMENTATION_PLAN.md section 4.2. Listing them here is the
    # --- record that the gap is known, not a claim that it is fine.
    "observations",       # section 7.5 device observation labels; no reader at all
    "isDevice",           # section 7.5 makes device participation load-bearing
    "restartability",     # section 7.4 retry rules have no mechanism
    "justification",      # transactional and permitsUninitialized name nothing
    "memoryType",         # section 7.1: write-back vs write-combining changes visibility
    "coherence",          # section 7.1: coherence domain, likewise
    "scope",              # ordering scope, with no registry to check it against
    "vocabularyVersion",  # nothing checks a profile's vocabulary version
    "package",            # the section 10 proof checklist is never consulted
    "issuer",             # ProtocolAuthority's issuer is carried, not checked
    "obligation",         # TerminalOutcome: dispositions are recorded, not enforced
    "disposition",
    # The resource layer is built ahead of its consumers, which arrive at M7 and
    # M9. Nothing outside Grass/Resource projects any of it yet.
    "combine",
    "alternative",
    "zero",
    "le",
    "laws",
    "axis",
    "limit",
    "carrier",
    "exhaustion",
    "lifecycle",
}

def fields_of(path: Path) -> list[tuple[str, str, int]]:
    """Yield (structure, field, line) for every structure field in one file.

    A structure runs until `deriving` or until a line at column zero that is not
    blank. Field docstrings are skipped rather than treated as the end -- an
    earlier version ended the structure at the first `/--`, which meant it saw
    almost no fields and reported a clean tree. It was caught by probing it
    against a field already known to have no reader, which is the only way to
    tell a working audit from a silent one.
    """
    out: list[tuple[str, str, int]] = []
    current: str | None = None
    in_doc = False
    for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        stripped = line.strip()
        if in_doc:
            if "-/" in stripped:
                in_doc = False
            continue
        if stripped.startswith("/-"):
            if "-/" not in stripped:
                in_doc = True
            continue
        match = STRUCTURE.match(line)
        if match:
            current = match.group(1)
            continue
        if current is None:
            continue
        if stripped.startswith("deriving") or (stripped and not line.startswith(" ")):
            current = None
            continue
        declaration = DECL.match(line)
        if declaration:
            out.append((current, declaration.group(1), number))
    return out


def main() -> int:
    corpus = {path: path.read_text(encoding="utf-8") for path in SOURCES}
    unread: list[str] = []
    for path, _ in corpus.items():
        for structure, field, line in fields_of(path):
            if field in ALLOWED:
                continue
            if any(structure.endswith(suffix) for suffix in PROOF_BUNDLES):
                continue
            projection = re.compile(r"\.%s\b" % re.escape(field))
            binder = re.compile(r"\b%s\s*:=\s*[a-z_(]" % re.escape(field))
            readers = 0
            for other, text in corpus.items():
                readers += len(projection.findall(text))
                if other != path:
                    readers += len(binder.findall(text))
            if readers == 0:
                unread.append(
                    f"  {path.relative_to(ROOT).as_posix()}:{line}: "
                    f"{structure}.{field} is declared and nothing reads it"
                )

    if unread:
        print("\n".join(sorted(unread)))
        print("consulted audit: declared facts with no reader\n")
        print(
            f"{len(unread)} unread field(s). Either consult the field, delete it, "
            "or add it to ALLOWED with the reason it is carried."
        )
        return 1
    print("consulted audit: every declared field has a reader")
    return 0


if __name__ == "__main__":
    sys.exit(main())
