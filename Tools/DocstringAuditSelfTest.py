"""Falsifying tests for `Tools/DocstringAudit.py`.

A gate that is never tested against inputs it should *reject* is a gate that
can silently stop biting. This one already did once: an earlier version passed
a claim citing an invented theorem name, which is the exact defect its own
header gives as its reason for existing, and nothing noticed until a reviewer
constructed the case by hand.

So each case here is a sentence the tool must reach a stated verdict on, and
four of them are rejections. The specification and module corpora are the real
ones, read from `docs/` and from the tree, because the point of several cases is
*which* names those corpora supply -- nouns yes, proofs no -- and a synthetic
corpus would only test that the test agrees with itself.

## Why every case declares whether it is a claim

An acceptance can happen two ways: the sentence was checked and its names
resolved, or the sentence was never checked at all. Only the first is evidence,
and the second is how a case goes quietly vacuous. That happened while these
tests were being written. A module-resolution case was phrased "`X` cannot state
a handle width"; "cannot state" is one of the tool's hedges, so the sentence was
skipped and the case passed regardless of what module resolution did -- it still
passed with `module_names` mutated to return nothing, which is exactly the
mutation it existed to catch.

`is_claim` is checked against the tool's own claim-word and hedge filters, so a
case that stops reaching the check now fails rather than passing.

Run: python Tools/DocstringAuditSelfTest.py
"""

import contextlib
import io as _io
import sys
import tempfile
from pathlib import Path

import importlib.util

_spec = importlib.util.spec_from_file_location(
    "docstring_audit", Path(__file__).with_name("DocstringAudit.py"))
audit = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(audit)

# A stand-in for the build's declaration list. Synthetic, because these cases
# are about the specification and module halves of resolution; the build half is
# exercised every time the audit runs for real.
KNOWN = {"encode", "Bag", "cons_injective_right", "Prop", "Type", "Sort"}

# (name, sentence, expected finding substring or None, reaches the check)
CASES = [
    (
        "invented theorem name",
        "`encode` ensures every address has one encoding, as proved by "
        "`encodeMem_is_canonical_over_addresses`.",
        "look like declarations",
        True,
    ),
    (
        "theorem the specification plans but nothing proves",
        "Emission ensures the artifact is sound, as proved by "
        "`emitted_sound`.",
        "look like declarations",
        True,
    ),
    (
        "vocabulary the specification declares",
        "`Bag` ensures `ProcessSpec.Step` keeps multiplicity.",
        None,
        True,
    ),
    (
        "declaration in the build",
        "`cons_injective_right` ensures the remainder is unique.",
        None,
        True,
    ),
    (
        "module path alone does not enforce anything",
        "`Grass.Platform.Win32.Console` ensures every handle has a width.",
        "names no enforcing type",
        True,
    ),
    (
        "module path beside a real enforcer",
        "`Grass.Platform.Win32.Console` ensures the remainder is unique, by "
        "`cons_injective_right`.",
        None,
        True,
    ),
    (
        "fabricated dotted theorem laundered through a module path",
        "`Grass.Platform.Win32.Console` ensures every write transfers every "
        "requested byte, as proved by `StdHandleId.write_is_total`.",
        "knows no such declaration",
        True,
    ),
    (
        "bare claim laundered through a module path",
        "`Tools.DeclNames` ensures no docstring can name a declaration that "
        "does not exist.",
        "names no enforcing type",
        True,
    ),
    (
        "module path the tree does not contain",
        "`Grass.Platform.Win10.X64` ensures the ABI is selected.",
        "knows no such declaration",
        True,
    ),
    (
        "hedge in a subordinate clause does not exempt the main clause",
        "The console ensures a caller never observes a short write, which an "
        "earlier draft of the module could not do.",
        "names no enforcing type",
        True,
    ),
    (
        "a stray quotation does not make a sentence a citation",
        "This ensures the encoding is unique, per docs/FOUNDATION.md law "
        "\"18\".",
        "names no enforcing type",
        True,
    ),
    (
        "a genuine quotation of a normative document is exempt",
        "docs/FOUNDATION.md says \"a specification cannot observe a schedule "
        "fact\".",
        None,
        False,
    ),
    (
        "a sort is not an enforcer",
        "`Prop` ensures the invariant holds.",
        "names no enforcing type",
        True,
    ),
    (
        "a lowercase milestone token does not exempt",
        "This ensures the encoding is unique for m4 inputs.",
        "names no enforcing type",
        True,
    ),
    (
        "a real milestone reference is a hedge",
        "M4 ensures the encoding is unique.",
        None,
        False,
    ),
    (
        "claim naming nothing",
        "This ensures the encoding is unique.",
        "names no enforcing type",
        True,
    ),
    (
        "hedged claim",
        "This is intended to ensure the encoding is unique.",
        None,
        False,
    ),
]


def reaches_check(sentence: str) -> bool:
    """Whether the tool treats this sentence as a claim at all.

    Delegated rather than reimplemented. Everywhere else in this file, using
    the code under test to check the code under test would hide the bug; here
    it is the only correct source, because the question is not "is the gate
    right" but "did this case exercise the gate", and only the gate can answer
    that. A mirrored copy drifted the moment the exemptions changed and turned
    two real cases into false failures.
    """
    return audit.is_checked_claim(sentence)


def run_one(tmp: Path, sentence: str, specs, modules, cited) -> list[str]:
    path = tmp / "Case.lean"
    path.write_text("/-!\n" + sentence + "\n-/\n", encoding="utf-8")
    return audit.check(path, KNOWN, specs, modules, cited)


# What the gate must still be *looking at*. Every case above calls `check`
# directly, so none of them says anything about scope -- and a reviewer showed
# how much that leaves open. Narrowing `doc_blocks` to `/-!` drops all 1717
# declaration docstrings and 70% of the claim sentences; narrowing the audited
# roots to one subdirectory audits 7 modules instead of 57; `main` discarding
# its findings makes the gate unable to fail at all. Every one of those left the
# case list green.
#
# Floors, not exact counts: the corpus grows, and a ratchet that had to be
# edited on every commit would be edited without being read. Raise them in the
# same reviewed change that grows the corpus.
MINIMUM_FILES = 55
MINIMUM_DOC_BLOCKS = 1800
MINIMUM_CLAIM_SENTENCES = 110
MINIMUM_DECLARATION_DOCSTRINGS = 1600


def reporting_acts_on_findings() -> list[str]:
    """A gate that cannot fail is worse than no gate."""
    failures = []
    # `report` writes through `sys.stdout.buffer`, so the sink needs a
    # real byte layer; `StringIO` has none.
    sink = _io.TextIOWrapper(_io.BytesIO(), encoding="utf-8")
    with contextlib.redirect_stdout(sink):
        with_findings = audit.report(["Some/File.lean:1: a finding"], {})
        without = audit.report([], {})
    if with_findings != 1:
        failures.append(
            f"reporting returned {with_findings} with a finding in hand; "
            "the audit would exit 0 on a tree full of unbacked claims")
    if without != 0:
        failures.append(
            f"reporting returned {without} with nothing found; a gate that "
            "fails on a clean tree gets switched off")
    return failures


def main_acts_on_findings() -> list[str]:
    """`main` must hand `report` what it actually found.

    Testing `report` alone moved the untested boundary rather than closing
    it: mutating `main` to call `report([], cited)` left the gate unable to
    fail and left every other case green. So `main` is run here against a
    one-file stub corpus, with the expensive oracles stubbed out, and its
    exit code is the assertion.
    """
    failures = []
    saved = (audit.declaration_names, audit.specification_names,
             audit.module_names, audit.audited_roots)
    sink = _io.TextIOWrapper(_io.BytesIO(), encoding="utf-8")
    try:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "Bad.lean").write_text(
                "/-!" + chr(10)
                + "This ensures the encoding is unique." + chr(10)
                + "-/" + chr(10),
                encoding="utf-8")
            audit.declaration_names = lambda: set(KNOWN)
            audit.specification_names = lambda: {}
            audit.module_names = lambda: set()
            audit.audited_roots = lambda: [root]
            with contextlib.redirect_stdout(sink):
                code = audit.main()
            if code != 1:
                failures.append(
                    f"main() returned {code} over a corpus whose only "
                    "docstring is an unbacked claim; the gate cannot fail")
            (root / "Bad.lean").unlink()
            with contextlib.redirect_stdout(sink):
                clean = audit.main()
            if clean != 0:
                failures.append(
                    f"main() returned {clean} over an empty corpus; a gate "
                    "that fails on a clean tree gets switched off")
    finally:
        (audit.declaration_names, audit.specification_names,
         audit.module_names, audit.audited_roots) = saved
    return failures


def corpus_shape() -> list[str]:
    """Check the gate still reads the corpus it is credited with reading."""
    failures = []
    roots = audit.audited_roots()
    if Path("Grass") not in roots:
        failures.append(
            f"the audit's roots are {roots}; Grass/ is the library and has to "
            "be among them")
    # Asked of the gate, not recomputed here: a floor derived independently
    # measures the tree, and the gate can be narrowed without moving it.
    files = audit.audited_files()
    blocks = 0
    claims = 0
    declaration_docstrings = 0
    for path in files:
        source = path.read_text(encoding="utf-8", errors="replace")
        declaration_docstrings += source.count("/--")
        for _, block in audit.doc_blocks(source):
            blocks += 1
            for sentence in audit.sentences(block):
                if reaches_check(sentence):
                    claims += 1
    for name, have, want in [
        ("files audited", len(files), MINIMUM_FILES),
        ("doc blocks parsed", blocks, MINIMUM_DOC_BLOCKS),
        ("claim sentences reaching the check", claims,
         MINIMUM_CLAIM_SENTENCES),
        ("declaration docstrings in the corpus", declaration_docstrings,
         MINIMUM_DECLARATION_DOCSTRINGS),
    ]:
        if have < want:
            failures.append(
                f"{name}: {have}, below the reviewed floor of {want}. The gate "
                "is reading less than it was reviewed against; if the "
                "reduction is deliberate, lower the floor in the same change.")
    return failures


def main() -> int:
    specs = audit.specification_names()
    modules = audit.module_names()

    failures = []
    # The corpora must have the shape these cases depend on.
    if "ProcessSpec.Step" not in specs:
        failures.append(
            "specification corpus lost `ProcessSpec.Step`; it is a structure "
            "field in docs/PROCESS.md and vocabulary resolution needs it")
    if "emitted_sound" in specs:
        failures.append(
            "specification corpus admitted `emitted_sound`; it is a planned "
            "theorem and only the build may supply proofs")
    if "Grass.Platform.Win32.Console" not in modules:
        failures.append(
            "module list lost Grass.Platform.Win32.Console; module resolution "
            "reads paths off disk and a case below depends on it")
    if "Grass.Platform.Win10.X64" in modules:
        failures.append(
            "module list contains Grass.Platform.Win10.X64, the spelling "
            "docs/MODULES.md replaced; a rejection case below would then pass "
            "for the wrong reason")

    with tempfile.TemporaryDirectory() as raw:
        tmp = Path(raw)
        for name, sentence, expected, is_claim in CASES:
            if reaches_check(sentence) != is_claim:
                failures.append(
                    f"{name}: the case declares is_claim={is_claim} but the "
                    "tool's claim-word and hedge filters disagree. A case that "
                    "does not reach the check proves nothing about what the "
                    "check does.")
                continue
            cited: dict[str, str] = {}
            findings = run_one(tmp, sentence, specs, modules, cited)
            if expected is None:
                if findings:
                    failures.append(
                        f"{name}: expected no finding, got {findings!r}")
            elif not any(expected in f for f in findings):
                failures.append(
                    f"{name}: expected a finding containing {expected!r}, "
                    f"got {findings!r}")
            if name.startswith("vocabulary") and "ProcessSpec.Step" not in cited:
                failures.append(
                    "vocabulary case resolved but was not reported; a "
                    "specification-resolved citation must stay visible")

    failures.extend(corpus_shape())
    failures.extend(reporting_acts_on_findings())
    failures.extend(main_acts_on_findings())

    if failures:
        print("docstring audit self-test: FAILED\n")
        for failure in failures:
            print("  " + failure)
        return 1
    rejects = sum(1 for _, _, expected, _ in CASES if expected)
    print(f"docstring audit self-test: {len(CASES)} cases, "
          f"{rejects} rejections and {len(CASES) - rejects} "
          "acceptances as specified")
    return 0


if __name__ == "__main__":
    sys.exit(main())
