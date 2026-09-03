#!/usr/bin/env python3
"""Report structure fields whose name is never projected anywhere.

Six rounds of adversarial review on the memory layer found eight defects that had
already passed a merge review, and all but one had the same shape: the model
carries a fact and nothing consults it. `Obligation.owner`, so any context could
discharge any duty. `Substep.faults`. `AccessIntent.isDevice`, which section 7.5
makes load-bearing.

**What this checks, exactly.** For each field name declared in a `structure`, it
searches the sources for the token `.name`. If that token never appears, the field
is reported. That is a *lexical* property and it is weaker than "nothing reads
this field" in ways worth naming, because an earlier version of this file
advertised the stronger reading and review corrected it:

- It keys on the field name, not on the declaring structure. Two structures with a
  field of the same name are indistinguishable, so a projection of one satisfies
  the other. Lean would need to be elaborated to do better; a text scan cannot.

  That also defeats the **allowlist**, which is not obvious and which review had to
  point out. `AccessDescriptor.restartability` is listed below as a genuine gap with
  no reader — and deleting the entry changes nothing, because
  `OperationFacets.restartability` is projected elsewhere and satisfies the name.
  So an allowlist entry can record a judgement the tool could never have needed, and
  the gap it documents can be unreportable. Read an entry as a note to a human, not
  as a suppression the tool relies on.
- It cannot tell a projection from a suffix that merely looks like one.
- Comments and string literals are stripped before scanning, so prose mentioning
  `.owner` no longer counts as a reader. That was a real false negative.
- A construction `name := value` is a write, not a read, and is not counted. That
  was also a real false negative: an external constructor made an unread field
  pass.

So a clean run means **no declared field name is entirely absent from the
sources**. It does not mean every field is meaningfully consumed, and it is not
evidence that the defect class is closed. It is one cheap net over a class that
six rounds of human-style review kept missing, and it under-reports by design.

The allowlist is where "carried deliberately without a reader" is recorded, with a
reason per entry. An unlisted field with no reader fails the build, so the
judgement is made once rather than rediscovered.

`--self-test` seeds each false-negative class this file claims to have closed and
asserts the tool still reports the field. Run it after changing the scanner; a
silent audit is worse than no audit, and this one was silent on its first version.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECLARED_IN = sorted((ROOT / "Grass").rglob("*.lean"))
# Readers are looked for in the fixtures too: a field a fixture projects is read,
# and excluding them made AuditViolation.class_ look inert when Tests/ reads it.
READERS_IN = DECLARED_IN + sorted((ROOT / "Tests").rglob("*.lean"))

# Only `structure` declarations are scanned. `class` fields and inductive
# constructor parameters are not, so an allowlist entry naming one of those records
# a judgement about something this tool could never report. Three such entries were
# removed; that removal was **partial**, and review said so: eight entries below
# (`combine`, `alternative`, `zero`, `le`, `laws`, `limit`, `exhaustion`,
# `lifecycle`) name fields that appear on the `HasResourceAxis`/`HasResourceLimit`
# *classes* as well as on the `ResourceLimit` structure, so each is doing work for
# the structure and none for the class. `Grass/Resource/Algebra.lean`'s
# `ResourceModel.algebra` is a live instance of this tool's own defect class that it
# cannot see for the same reason.
#
# Extending the scan to classes would be a real change, not a regex tweak, because a
# class field is consumed through instance resolution that a text scan cannot see.
# `[A-Za-z]`, not `[a-z]`: a capital-initial field is a field. `ResourceLimit.Value`
# and `HasResourceAxis.Value` were outside the scan entirely, and both are live
# structure fields with no projection anywhere -- exactly what this tool reports,
# missed by a character class. Review found it.
DECL = re.compile(r"^\s{2,}(?:private\s+)?([A-Za-z][A-Za-z0-9_']*)\s*:\s*[^=]")
STRUCTURE = re.compile(r"^\s*(?:private\s+)?structure\s+([A-Za-z_][A-Za-z0-9_.']*)")

# Fields deliberately carried without a reader. Every entry states why, and the
# entry is the record that the decision was made.
# A structure whose fields are propositions bundles proof obligations. Not reading
# such a field is the normal case -- its purpose is that a constructor had to
# discharge it -- so these are skipped by structure rather than field.
PROOF_BUNDLES = ("WellFormed", "Recognized", "Laws")

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
    # --- Carried without a projection. Being listed here is not "this is fine":
    # --- it is the record that someone read the corpus and decided. The reasons
    # --- differ, and conflating them is how the first version of section 4.2 of
    # --- docs/MEMORY_IMPLEMENTATION_PLAN.md called four milestone boundaries
    # --- defects.
    #
    # Genuine gaps: a corpus requirement, no consumer, and no milestone that owns
    # them. Recorded as owed in section 4.2.
    "observations",       # section 7.5 device observation labels; no reader at all
    "restartability",     # section 7.4 retry rules have no mechanism
    "vocabularyVersion",  # one version exists, so nothing to compare against yet
    #
    # Not gaps: the consumer is a later milestone or another layer, and the field
    # is carried exactly as its own document requires.
    "memoryType",         # section 7.1 requires the event to carry it, and it does
    "coherence",          # likewise; the rules are section 7.2's, which is M8
    "package",            # section 10 gates VerifiedProgram, not this transition
    "issuer",             # its docstring records this as M10 profile closure
    "obligation",         # TerminalOutcome awaits terminal accounting
    "disposition",   # TerminalOutcome, likewise
    # Proof obligations: their purpose is that a constructor had to discharge
    # them, so nothing projects them. The structure-suffix rule above misses these
    # because they sit on structures with other names.
    "readsFull",
    "writesFull",
    "vocabularyWellFormed",
    # Diagnostic provenance carried into the trace for a report to read, never
    # dispatched on, like `id` and `origin` above.
    "cause",
    "substep",
    # The resource layer is built ahead of its consumers, which arrive at M7 and
    # M9. Nothing outside Grass/Resource projects any of it yet.
    # A field whose *type* is the point: every other field of `ResourceLimit` is
    # typed by it, so it is consumed by the structure's own signature and cannot be
    # "projected" in the sense this tool looks for. Found by widening the field
    # pattern to accept a capital initial, which is what made it visible at all.
    "Value",
    "combine",
    "alternative",
    "zero",
    "le",
    "laws",
    "limit",
    "exhaustion",
    "lifecycle",
}

BLOCK = re.compile(r"/-.*?-/", re.DOTALL)
LINE = re.compile(r"--.*?$", re.MULTILINE)
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')


def scannable(text: str) -> str:
    """Strip block comments, line comments, and string literals.

    Prose mentioning `.owner` and a docstring quoting a field name are not
    readers, and counting them was a false negative review found.
    """
    return STRING.sub('""', LINE.sub("", BLOCK.sub(" ", text)))


def fields_in(text: str) -> list[tuple[str, str, int]]:
    """Yield (structure, field, line) for every structure field in one source.

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
    for number, line in enumerate(text.splitlines(), 1):
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


def analyse(raw: dict[str, str],
            readers: dict[str, str] | None = None) -> list[str]:
    """Report `path:line: Structure.field` for every field name never projected.

    Takes the sources as text so the self-test can seed them. Only a projection
    counts: `name := value` is construction, which is a write, and counting it let
    an external constructor make an unread field pass.
    """
    corpus = {name: scannable(text) for name, text in (readers or raw).items()}
    unread: list[str] = []
    for name, text in raw.items():
        for structure, field, line in fields_in(text):
            if field in ALLOWED:
                continue
            if any(structure.endswith(suffix) for suffix in PROOF_BUNDLES):
                continue
            projection = re.compile(r"\.%s\b" % re.escape(field))
            if not any(projection.search(body) for body in corpus.values()):
                unread.append(
                    f"  {name}:{line}: {structure}.{field} is declared and "
                    "its name is never projected"
                )
    return unread


def self_test() -> int:
    """Seed each false-negative class this file claims to have closed.

    A silent audit is worse than no audit, and the first version of this file was
    silent -- it treated a field docstring as the end of a structure, saw almost
    nothing, and reported a clean tree. These cases fail loudly if the scanner
    stops discriminating.
    """
    decl = 'structure Probe where\n  /-- doc -/\n  quarry : Nat\n'
    cases = [
        ("bare declaration", {"a.lean": decl}, True),
        ("real projection", {"a.lean": decl, "b.lean": "def f (p : Probe) := p.quarry\n"}, False),
        # Multi-line and not beginning with `--`, so the line-comment rule cannot
        # strip it. The single-line `/-- ... -/` case this replaced *began* with
        # `--`, so LINE stripped it and the case passed with BLOCK deleted
        # outright -- a self-test that could not fail for the thing it named.
        # Every module comment under Grass/ is exactly this shape.
        ("block comment mentioning .quarry",
         {"a.lean": decl,
          "b.lean": "/-!\nA module comment about .quarry\nspanning lines.\n-/\ndef f := 1\n"},
         True),
        ("line comment mentioning .quarry",
         {"a.lean": decl, "b.lean": "-- reads .quarry eventually\ndef f := 1\n"}, True),
        ("string literal mentioning .quarry",
         {"a.lean": decl, "b.lean": 'def f := "look at .quarry"\n'}, True),
        ("construction only",
         {"a.lean": decl, "b.lean": "def p : Probe := { quarry := 3 }\n"}, True),
    ]
    # The reader corpus is a separate parameter and no case above exercises it:
    # each passes one dict, so `main` dropping the Tests/ readers would go
    # unnoticed -- which the file's own comment calls out as a fixed false
    # positive.
    reader_cases = [
        ("reader only in the reader corpus",
         {"a.lean": decl},
         {"a.lean": decl, "t.lean": "def f (p : Probe) := p.quarry\n"}, False),
        ("no reader in either corpus",
         {"a.lean": decl}, {"a.lean": decl}, True),
    ]
    failures = 0
    for label, sources, should_report in cases:
        reported = any("Probe.quarry" in line for line in analyse(sources))
        if reported != should_report:
            want = "reported" if should_report else "not reported"
            print(f"  SELF-TEST FAILED [{label}]: expected {want}")
            failures += 1

    for label, declared, readers, should_report in reader_cases:
        reported = any("Probe.quarry" in line for line in analyse(declared, readers))
        if reported != should_report:
            want = "reported" if should_report else "not reported"
            print(f"  SELF-TEST FAILED [{label}]: expected {want}")
            failures += 1

    # Documented blind spot, asserted so it cannot quietly become a silent pass
    # that someone mistakes for coverage. Distinguishing these needs elaboration.
    other = ('structure Probe where\n  /-- doc -/\n  quarry : Nat\n\n'
             'structure Decoy where\n  /-- doc -/\n  quarry : Nat\n')
    missed = not any("Probe.quarry" in line
                     for line in analyse({"a.lean": other,
                                          "b.lean": "def f (d : Decoy) := d.quarry\n"}))
    if not missed:
        print("  SELF-TEST FAILED [same-named field]: blind spot has changed; "
              "update the module docstring, which documents it as unhandled")
        failures += 1

    if failures:
        print(f"consulted audit self-test: {failures} failure(s)")
        return 1
    print("consulted audit self-test: all cases discriminate as documented")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    declared = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                for path in DECLARED_IN}
    readers = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
               for path in READERS_IN}
    unread = analyse(declared, readers)

    if unread:
        print("\n".join(sorted(unread)))
        print("consulted audit: declared facts with no reader\n")
        print(
            f"{len(unread)} unread field(s). Either consult the field, delete it, "
            "or add it to ALLOWED with the reason it is carried."
        )
        return 1
    print(
        "consulted audit: no declared field name is entirely unprojected "
        "(a lexical check; see the module docstring for what it does not cover)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
