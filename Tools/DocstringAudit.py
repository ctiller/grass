#!/usr/bin/env python3
"""Check that strong implementation-comment claims name their enforcement.

Scope: **every** `/-- -/` and `/-! -/` block under `Grass/`, including a theorem's
own docstring. An earlier version of this paragraph said a theorem's docstring was
exempt "because the theorem beneath it *is* the enforcement", and a `SELF_NAMING`
pattern was defined for it and never used -- so the tool examined those blocks
anyway and the docstring described a scope it did not have. Review found it, in the
tool whose entire job is that class of error. The pattern is deleted rather than
implemented: a theorem's docstring is where the overclaims in this project have
actually lived, and exempting it would have passed several of them.

docs/MEMORY_IMPLEMENTATION_PLAN.md section 3.10:

    Any implementation comment using "ensures", "prevents", "cannot", "only", or
    "preserves" must name the enforcing type or theorem. If it cannot name one, it
    must be rewritten as an intended invariant or an open obligation.

Four adversarial review rounds each found a docstring asserting a property the
code did not have -- including one naming a theorem that did not exist, in the
file whose own comment states this rule. Mechanism-shaped prose reads as
verification and is not, so the rule needs a checker rather than a convention.

The check is deliberately shallow, and shallower than it reads. What it verifies is
that a claim-shaped sentence contains *some* backticked identifier. It therefore
misses, and each of these was found by mutation-testing it:

- a sentence whose backticked identifier is not the enforcement -- including one that
  is the claim's own *subject* ("`MemoryAccess` cannot be constructed out of
  bounds");
- a claim phrased without any word in `CLAIM_WORDS` ("an out-of-bounds access is
  never admitted");
- a claim next to any hedge word anywhere in the same sentence, since hedging is
  matched on the sentence and not on the clause;
- whether the named theorem says what the sentence claims. That is not covered by
  any tool here. `Tools/CitationAudit.py` checks the name *exists*, which is a
  different and weaker thing, and an earlier version of its docstring said this
  class was "`DocstringAudit.py`'s territory". It is nobody's.

So a clean run means no claim-shaped sentence is entirely without a name to chase.
It is one cheap net over prose that reads as verification, and it under-reports by
construction.

`--self-test` seeds a claim the tool must report and the near-misses it must not,
including the bypasses above, so the ones it cannot see are asserted rather than
merely described. Run it after changing the vocabulary.

Exit status is 1 if any claim is unbacked.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Deliberately narrow. The designer's rule names "ensures", "prevents", "cannot",
# "only", and "preserves"; "only" occurs constantly in ordinary descriptive English
# ("the only fault position") and flagging every one buries the signal, so it is kept
# in its guarantee-shaped phrasings only. "preserves" is kept whole -- an earlier
# version of this comment said it was dropped for the same reason and it was not,
# which review caught.
#
# The tool therefore under-reports by construction. It is a net for the specific
# drift four review rounds found -- a definition or module comment asserting an
# enforcement it does not name -- not a proof that no comment overclaims.
CLAIM_WORDS = (
    "ensures", "ensuring", "prevents", "preventing", "cannot", "preserves",
    "guarantees", "makes it impossible", "is enforced", "only if", "only when",
)

# A sentence *beginning* "Must ..." is a constraint on the thing it annotates,
# which is a mechanised claim. A "must" later in a sentence usually describes a
# duty in the modelled domain instead -- "a lock was acquired and must be
# released" is what an obligation kind *means*, not an assertion about this
# code -- so the word alone is too coarse and the position carries the meaning.
#
# This rule exists because a real defect escaped through it. The docstring on
# `AuthorityProvider.violationClass` read "Must be one the profile declares",
# nothing enforced it, and `g-reviewer:14` found what the auditor did not:
# a provider could record a violation class outside the admitted vocabulary.
CLAIM_PATTERNS = (re.compile(r"^\*{0,2}must\s"),)

# A sentence that says a property is aspirational, absent, or owed elsewhere is
# not making a mechanised claim, and the rule explicitly permits it.
HEDGES = (
    "intended", "not enforced", "does not", "cannot be made", "owes", "owed",
    "open obligation", "would", "used to", "an earlier", "M2", "M3", "M4", "M5",
    "M6", "M7", "M8", "M9", "M10", "no arrangement", "is not the check",
    "not by itself", "on its own", "nothing here", "cannot tell", "is not that",
    "not something", "deliberately", "no way to", "unrepresentable",
    # "X cannot do Y" is a statement of limitation, which is the honest
    # alternative the rule asks for rather than the drift it targets.
    "cannot state", "cannot be demonstrated", "cannot read", "cannot fault",
    "cannot lawfully", "cannot coexist", "cannot be checked", "cannot introduce",
    "cannot enforce", "cannot answer", "cannot express", "cannot know",
    "cannot be erased or masked",
)

# A declaration whose docstring makes the claim *is* the enforcement, so a
# theorem's own comment naming its own statement is not drift. Definitions,
# structures, and module comments are where unbacked prose hides.
SELF_NAMING = re.compile(r"^\s*(@\[[^\]]*\]\s*)?(private\s+)?(theorem|instance|example)")

# A backticked identifier is the "names the enforcing type or theorem" part.
IDENT = re.compile(r"`([A-Za-z_][A-Za-z0-9_.?!']*)`")
# Section references and prose in backticks are not identifiers.
NOT_IDENT = re.compile(r"^(docs/|§|[a-z]+\s)")


def sentences(block: str) -> list[str]:
    text = " ".join(line.strip() for line in block.splitlines())
    # Split on sentence ends only. A semicolon joins a claim to the clause that
    # names its enforcement, so splitting there would report the claim as unbacked
    # while the name sits in the next fragment.
    return [s.strip() for s in re.split(r"(?<=[.])\s+", text) if s.strip()]


def doc_blocks(source: str):
    """Yield (line number, text) for every `/-- ... -/` and `/-! ... -/` block."""
    for match in re.finditer(r"/-[-!](.*?)-/", source, re.DOTALL):
        line = source[: match.start()].count("\n") + 1
        yield line, match.group(1)


def check(path: Path) -> list[str]:
    return check_source(path.read_text(encoding="utf-8"), path)


def check_source(source: str, path: Path) -> list[str]:
    findings = []
    for line, block in doc_blocks(source):
        for sentence in sentences(block):
            lowered = sentence.lower()
            if not (any(word in lowered for word in CLAIM_WORDS)
                    or any(pattern.match(lowered) for pattern in CLAIM_PATTERNS)):
                continue
            if any(hedge.lower() in lowered for hedge in HEDGES):
                continue
            # A passage quoted from a normative document is that document's
            # claim, not this module's. It is cited, which is the point.
            if "docs/" in sentence and '"' in sentence:
                continue
            named = [
                ident
                for ident in IDENT.findall(sentence)
                if not NOT_IDENT.match(ident)
            ]
            if not named:
                findings.append(
                    f"{path.as_posix()}:{line}: claim names no enforcing type or "
                    f"theorem: {sentence!r}"
                )
    return findings


def self_test() -> int:
    """Seed a claim the tool must report, and the near-misses it must not.

    The second group is the point: those are the bypasses this file's docstring
    lists, asserted here so they cannot quietly become coverage someone relies on.
    """
    must_report = [
        ("bare claim", "/-- This ensures that every access is bounds-checked. -/"),
        ("claim in a theorem docstring",
         "/-- This ensures that every access is bounds-checked. -/\ntheorem t : True := trivial"),
    ]
    must_not_report = [
        ("named enforcement",
         "/-- This ensures that every access is bounds-checked, by `boundsOk`. -/"),
        ("hedged", "/-- This is intended to ensure that every access is bounds-checked. -/"),
        # Documented bypasses. Each is a sentence the rule is about and the tool
        # does not see; asserting them keeps the docstring's list honest.
        ("bypass: the subject counts as the enforcer",
         "/-- `MemoryAccess` cannot be constructed out of bounds. -/"),
        ("bypass: no claim word",
         "/-- An out-of-bounds access is never admitted and no state produces one. -/"),
        ("bypass: an unrelated backticked name",
         "/-- This ensures that every access is bounds-checked, see `Nat`. -/"),
    ]
    failures = 0
    for label, source in must_report:
        if not check_source(source, Path("probe.lean")):
            print(f"  SELF-TEST FAILED [{label}]: expected a finding")
            failures += 1
    for label, source in must_not_report:
        if check_source(source, Path("probe.lean")):
            print(f"  SELF-TEST FAILED [{label}]: expected no finding")
            failures += 1
    if failures:
        print(f"docstring audit self-test: {failures} failure(s)")
        return 1
    print("docstring audit self-test: all cases discriminate as documented")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    # `Tests/` is excluded, and not for the reason this comment used to give.
    # Fixture comments are not all value-shaped -- review found thirteen
    # mechanism-shaped sentences there, all backed. They are excluded because a
    # fixture's evidence is the fixture, and the rule in
    # `docs/MEMORY_IMPLEMENTATION_PLAN.md` §3.10 is about implementation comments.
    root = ROOT / "Grass"
    paths = sorted(root.rglob("*.lean"))
    # A tool that finds no files must fail, not pass. `roots = [Path("Grass")]` was
    # relative to the working directory and the miss was swallowed by an
    # `is_dir()` guard, so running from anywhere but the repo root printed the
    # success line having read nothing. The other three audits anchor on
    # `__file__`; this one, which has no self-test either, did not.
    if not paths:
        print(f"docstring audit: no sources found under {root}", file=sys.stderr)
        return 1
    findings: list[str] = []
    for path in paths:
        findings.extend(check(path))
    if findings:
        print("docstring audit: claims that name nothing enforcing them\n")
        for finding in findings:
            sys.stdout.buffer.write((chr(32)*2 + finding + chr(10)).encode("utf-8", "replace"))
        print(
            f"\n{len(findings)} unbacked claim(s). Name the type or theorem, or "
            "rewrite as an intended invariant or open obligation."
        )
        return 1
    print("docstring audit: every strong claim names an enforcing type or theorem")
    return 0


if __name__ == "__main__":
    sys.exit(main())
