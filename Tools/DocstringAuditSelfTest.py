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

# A stand-in for what `documented_names` reads out of `docs/`. Synthetic for the
# same reason `KNOWN` is: these cases are about which resolution set a citation
# is allowed to use, not about whether the reader of `docs/` works.
DOCUMENTED = {"no_ingress_step_after_terminal"}

# (name, sentence, expected finding substring or None, reaches the check)
CASES = [
    (
        "citation rot outside a claim",
        "See `every_run_holds_the_root` in the preservation fixtures.",
        "cites",
        False,
    ),
    (
        "specification theorem cited outside a claim",
        "See `no_ingress_step_after_terminal` for the shape of the argument.",
        None,
        False,
    ),
    (
        "unbuilt name in a milestone note",
        "`asm_source_is_lowered` arrives with M4 and is not here yet.",
        None,
        False,
    ),
    (
        "prose word that is not a declaration name",
        "The result is left in `RAX` and the flags are clobbered.",
        None,
        False,
    ),
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
        # `sentences` used to split only on a bare period, so a sentence ending
        # `.)` never terminated and its hedge carried into the next one.
        "a hedge in a bracketed sentence does not carry to the next",
        "(Partial writes are intended to be modelled here.) The console "
        "ensures no caller observes a short write.",
        "names no enforcing type",
        # Two sentences, so the whole-text predicate is not meaningful for the
        # case as written -- `check` splits it and judges the second. The split
        # itself is asserted structurally in `parsers_do_not_lose_text`; this
        # case checks that the second sentence is then reported.
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


# A case declaring `is_claim=False` is no longer a case that goes unexamined.
# Since `stray_citations` was added, every sentence is read: a claim goes to the
# enforcement check, and everything else to the citation check. So `is_claim`
# now says *which* check a case exercises rather than whether it is checked at
# all, and the cases below use both settings deliberately.


def run_one(tmp: Path, sentence: str, specs, modules, cited) -> list[str]:
    path = tmp / "Case.lean"
    path.write_text("/-!\n" + sentence + "\n-/\n", encoding="utf-8")
    return audit.check(path, KNOWN, specs, modules, cited, DOCUMENTED)


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
            # Two files, with the offending one *second* in sorted
            # order. A reviewer truncated `main` to `audited_files()[:1]`;
            # every floor stayed green, because the floors ask what the gate
            # walks and `main` was free not to use it.
            (root / "AClean.lean").write_text(
                "/-!" + chr(10)
                + "`cons_injective_right` ensures the remainder is unique."
                + chr(10) + "-/" + chr(10),
                encoding="utf-8")
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
            (root / "AClean.lean").unlink()
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


def parsers_do_not_lose_text() -> list[str]:
    """The two parsers that decide what is even looked at.

    Both had defects that made whole passages invisible, which no case in the
    list above could reveal: a case is a sentence handed straight to `check`,
    so it never exercises how sentences and blocks are found in the first
    place.
    """
    failures = []
    nested = ("/-- The width is 32. /- see docs -/" + chr(10)
              + "The console ensures nothing. -/" + chr(10))
    blocks = [text for _, text in audit.doc_blocks(nested)]
    if len(blocks) != 1 or "ensures nothing" not in blocks[0]:
        failures.append(
            "doc_blocks lost text after a nested comment: Lean allows a block "
            "comment inside a doc comment, and everything past the inner "
            f"terminator would be audited by nothing. Got {blocks!r}")
    bracketed = ("(Partial writes are intended to be modelled here.) The "
                 "console ensures no caller observes a short write.")
    parts = audit.sentences(bracketed)
    if len(parts) != 2:
        failures.append(
            "sentences did not split at `.)`, so the first sentence's hedge "
            f"would exempt the second's claim. Got {parts!r}")
    return failures


def oracle_failure_is_fatal() -> list[str]:
    """A missing declaration list must stop the audit, not empty it.

    `declaration_names` says an audit that passes because it could not obtain
    the name list is worse than no audit. Nothing tested that, and a reviewer
    showed the subprocess-failure exit and the size floor could both be deleted
    together while every case stayed green.
    """
    import subprocess as _sub
    failures = []
    saved = _sub.run

    class Result:
        def __init__(self, code, out):
            self.returncode = code
            self.stdout = out
            self.stderr = ""

    for label, result in [
        ("a failing oracle", Result(1, "")),
        ("an oracle returning almost nothing", Result(0, "Grass.A" + chr(10))),
    ]:
        _sub.run = lambda *a, **k: result
        try:
            audit.declaration_names()
            failures.append(
                f"declaration_names accepted {label}; the audit would then "
                "report every real name as invented, or pass by knowing "
                "nothing")
        except SystemExit:
            pass
        finally:
            _sub.run = saved
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
    failures.extend(parsers_do_not_lose_text())
    failures.extend(oracle_failure_is_fatal())
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
