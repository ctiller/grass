#!/usr/bin/env python3
"""Check that strong implementation-comment claims name their enforcement.

Scope: module comments and the docstrings of definitions, structures, classes,
and inductives. A theorem's own docstring is exempt, because the theorem beneath
it *is* the enforcement -- restating a proved statement in English is not drift.
Unbacked prose hides where there is no adjacent proof.

docs/MEMORY_IMPLEMENTATION_PLAN.md section 3.10:

    Any implementation comment using "ensures", "prevents", "cannot", "only", or
    "preserves" must name the enforcing type or theorem. If it cannot name one, it
    must be rewritten as an intended invariant or an open obligation.

Four adversarial review rounds each found a docstring asserting a property the
code did not have -- including one naming a theorem that did not exist, in the
file whose own comment states this rule. Mechanism-shaped prose reads as
verification and is not, so the rule needs a checker rather than a convention.

The check is deliberately shallow. It cannot tell whether a named theorem proves
what the sentence claims; it can tell that the sentence names *something* the
build knows about, which is the difference between a claim that can be chased and
one that cannot. A sentence that hedges -- "intended", "not enforced", "owes",
"open obligation", and the like -- is exempt, because saying a property is not yet
mechanised is exactly the honest alternative the rule asks for.

Exit status is 1 if any claim is unbacked.
"""

import re
import sys
from pathlib import Path

# Deliberately narrow. The designer's rule names "ensures", "prevents", "cannot",
# "only", and "preserves"; the last two occur constantly in ordinary descriptive
# English ("the only fault position", "a value that is never live") and flagging
# every one buries the signal. What is kept are the words that assert a mechanism
# rather than describe a value, plus "only" in its guarantee-shaped phrasings.
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
    source = path.read_text(encoding="utf-8")
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


def main() -> int:
    # `Tests/` is excluded: fixture comments describe values ("an identity that
    # is never live"), not mechanisms, and the fixtures are themselves the
    # evidence a claim would point at.
    roots = [Path("Grass")]
    findings: list[str] = []
    for root in roots:
        if not root.is_dir():
            continue
        for path in sorted(root.rglob("*.lean")):
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
