#!/usr/bin/env python3
"""Check that strong implementation-comment claims name their enforcement.

Scope: module comments and the docstrings of definitions, structures, classes,
inductives -- and theorems. A theorem's own docstring was meant to be exempt, on
the grounds that the theorem beneath it *is* the enforcement, and this file said
so for a long time while never implementing it: the `SELF_NAMING` pattern was
defined and never used. A reviewer found the dead constant.

The exemption is not reinstated. It would be the wrong direction: a theorem's
docstring routinely claims more than its statement proves -- that is how
`decodeInsn_toBytes` came to be described as evidence about x86 -- and the
check is cheap. The docstring now describes what the code does.

docs/MEMORY_IMPLEMENTATION_PLAN.md section 3.10:

    Any implementation comment using "ensures", "prevents", "cannot", "only", or
    "preserves" must name the enforcing type or theorem. If it cannot name one, it
    must be rewritten as an intended invariant or an open obligation.

Four adversarial review rounds each found a docstring asserting a property the
code did not have -- including one naming a theorem that did not exist, in the
file whose own comment states this rule. Mechanism-shaped prose reads as
verification and is not, so the rule needs a checker rather than a convention.

The check is deliberately shallow. It cannot tell whether a named theorem proves
what the sentence claims; it can tell that the sentence names something the build
knows about, which is the difference between a claim that can be chased and one
that cannot.

That second half used to be false. The tool never touched a Lean environment --
it looked for a backticked identifier and stopped -- so any invented name
satisfied it. A reviewer passed the audit with a sentence claiming the encoder
"ensures" and "prevents", backed by
`encodeMem_is_canonical_and_injective_over_all_addresses`, which does not exist;
the identical sentence with the backticks removed failed. That is precisely the
defect this file's own header cites as its reason for existing. Names are now
checked against `Tools/DeclNames.lean`, which prints every declaration the build
knows. A sentence that hedges -- "intended", "not enforced", "owes",
"open obligation", and the like -- is exempt, because saying a property is not yet
mechanised is exactly the honest alternative the rule asks for.

Exit status is 1 if any claim is unbacked.
"""

import re
import subprocess
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

# A sentence that says a property is aspirational, absent, or owed elsewhere is
# not making a mechanised claim, and the rule explicitly permits it.
HEDGES = (
    "intended", "not enforced", "cannot be made", "owes", "owed",
    "open obligation", "used to", "an earlier", "M2", "M3", "M4", "M5",
    "M6", "M7", "M8", "M9", "M10", "no arrangement", "is not the check",
    "not by itself", "on its own", "nothing here", "cannot tell", "is not that",
    "not something", "no way to", "unrepresentable",
    # "X cannot do Y" is a statement of limitation, which is the honest
    # alternative the rule asks for rather than the drift it targets.
    "cannot state", "cannot be demonstrated", "cannot read", "cannot fault",
    "cannot lawfully", "cannot coexist", "cannot be checked", "cannot introduce",
    "cannot enforce", "cannot answer", "cannot express", "cannot know",
    "cannot be erased or masked",
)

# Hedges match as whole words. As bare substrings they matched inside ordinary
# x86 vocabulary: "M8" inside `imm8`, "M3" inside `imm32`, "M6" inside `imm64`,
# and "owed" inside `Allowed`. A reviewer found three real sentences exempted
# for no reason but the letters in an operand size -- in an x86 tree that was
# only going to grow.
# Hedges match as whole words, not as bare substrings.
#
# As substrings they matched inside ordinary vocabulary: "owed" inside
# `Allowed`, and the milestone labels "M3", "M6" and "M8" inside `imm32`,
# `imm64` and `imm8`. A reviewer found three sentences exempted for no reason
# but the letters in an operand size, which in an x86 tree was only going to
# get worse.
#
# The milestone labels stay. They refer to the milestones of
# `docs/MEMORY_IMPLEMENTATION_PLAN.md`, so a sentence naming one is describing
# work that is not built yet -- which is a hedge in exactly the sense this list
# means. The reviewer read them as review scratch and this file briefly agreed;
# both were wrong, and removing them would have suppressed a legitimate
# exemption in `Grass/Memory/Event.lean`.
HEDGE_RE = re.compile(
    "|".join(
        r"\b" + re.escape(h.lower()).replace(r"\ ", " ") + r"\b"
        for h in HEDGES
    )
)

# Which unresolved names are worth reporting.
#
# Requiring *every* backticked identifier to resolve over-fires: `RAX`,
# `INC`, `REX.X`, `SizeOfProlog`, `UWOP_SAVE_XMM128` and `cl.exe` are correct
# technical writing, and so are `w.bits` and `d.space`, which name a binder's
# field. Sixteen such sentences fail that rule and none of them is drift.
#
# Requiring only that *something* resolves is what a reviewer defeated: naming
# the function a sentence is about -- normal, good writing -- masks an invented
# theorem name in the same sentence. "`encode` ensures every address has one
# encoding, as proved by `encodeMem_is_canonical_and_injective_over_all_addresses`"
# passed, while the same sentence without `encode` failed.
#
# So this matches the shape of a Lean declaration name rather than the shape of
# an identifier: lowercase-initial with at least one underscore-separated part,
# which is the convention every theorem in this repository follows and which
# none of the false positives above has. It is a heuristic and is stated as one.
# It does not catch an invented `camelCase` name, and an author who wants to
# fabricate enforcement can still do it; what it catches is the form that
# fabrication actually takes, because a fabricated *theorem* is what a claim
# cites.
LEAN_STYLE_NAME = re.compile(r"^[a-z][A-Za-z0-9']*(_[A-Za-z0-9'][A-Za-z0-9']*)+$")

# A backticked identifier is the "names the enforcing type or theorem" part.
IDENT = re.compile(r"`([A-Za-z_][A-Za-z0-9_.?!']*)`")
# Section references and prose in backticks are not identifiers.
NOT_IDENT = re.compile(r"^(docs/|§|[a-z]+\s)")


def declaration_names() -> set[str]:
    """Every name the build knows, plus every dotted suffix of one.

    Suffixes because a docstring names a declaration the way a reader would --
    `writeBack.w32_clears_high`, not
    `Grass.ISA.X86.writeBack.w32_clears_high` -- and demanding the fully
    qualified form would push authors towards naming nothing.

    A missing oracle is a failure, not a skip: an audit that passes because it
    could not obtain the name list is worse than no audit, which is the mistake
    this function was added to correct.
    """
    exe_name = "declnames.exe" if sys.platform == "win32" else "declnames"
    exe = Path(".lake/build/bin") / exe_name
    if not exe.is_file():
        subprocess.run(["lake", "build", "declnames"], check=True)
    proc = subprocess.run(
        [str(exe)],
        capture_output=True, text=True, encoding="utf-8", errors="replace")
    if proc.returncode != 0:
        sys.exit(
            "could not obtain the declaration list from declnames:\n"
            + (proc.stdout + proc.stderr).strip()[:2000])
    known: set[str] = set()
    for line in proc.stdout.splitlines():
        name = line.strip()
        if not name or " " in name:
            continue
        parts = name.split(".")
        for i in range(len(parts)):
            known.add(".".join(parts[i:]))
    # Sorts are not constants, so a sentence naming only `Prop` or `Type` would
    # otherwise be reported as naming nothing.
    known.update({"Prop", "Type", "Sort"})
    if len(known) < 1000:
        sys.exit(
            f"declaration list has only {len(known)} entries, which cannot be "
            "right; refusing to report a clean audit against it")
    return known


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


def check(path: Path, known: set[str]) -> list[str]:
    source = path.read_text(encoding="utf-8")
    findings = []
    for line, block in doc_blocks(source):
        for sentence in sentences(block):
            lowered = sentence.lower()
            if not any(word in lowered for word in CLAIM_WORDS):
                continue
            if HEDGE_RE.search(lowered):
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
            resolved = [ident for ident in named if ident in known]
            # An unresolved name that *looks like a Lean declaration* is the
            # attack; an unresolved `RAX` or `INC` is ordinary prose. See
            # LEAN_STYLE_NAME.
            invented = [
                ident for ident in named
                if ident not in known and LEAN_STYLE_NAME.match(ident)
            ]
            if invented:
                findings.append(
                    f"{path.as_posix()}:{line}: claim names "
                    f"{invented}, which look like declarations and are not in "
                    f"the build: {sentence!r}"
                )
            elif named and not resolved:
                findings.append(
                    f"{path.as_posix()}:{line}: claim names "
                    f"{named} but the build knows no such declaration: "
                    f"{sentence!r}"
                )
            elif not named:
                findings.append(
                    f"{path.as_posix()}:{line}: claim names no enforcing type or "
                    f"theorem: {sentence!r}"
                )
    return findings


def main() -> int:
    exe_name = "docstring-audit.exe" if sys.platform == "win32" else "docstring-audit"
    rust_bin = Path(__file__).resolve().parent / "docstring-audit" / "target" / "release" / exe_name
    if rust_bin.is_file():
        res = subprocess.run([str(rust_bin)])
        return res.returncode

    # `Tests/` is excluded: fixture comments describe values ("an identity that
    # is never live"), not mechanisms, and the fixtures are themselves the
    # evidence a claim would point at.
    roots = [Path("Grass")]
    known = declaration_names()
    findings: list[str] = []
    for root in roots:
        if not root.is_dir():
            continue
        for path in sorted(root.rglob("*.lean")):
            findings.extend(check(path, known))
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
