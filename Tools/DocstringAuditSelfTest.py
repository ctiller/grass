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
        "module path the tree contains",
        "`Grass.Platform.Win32.Console` ensures every handle has a width.",
        None,
        True,
    ),
    (
        "module path the tree does not contain",
        "`Grass.Platform.Win10.X64` ensures the ABI is selected.",
        "knows no such declaration",
        True,
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
    """Whether the tool treats this sentence as a claim at all."""
    lowered = sentence.lower()
    if not any(word in lowered for word in audit.CLAIM_WORDS):
        return False
    return not audit.HEDGE_RE.search(lowered)


def run_one(tmp: Path, sentence: str, specs, modules, cited) -> list[str]:
    path = tmp / "Case.lean"
    path.write_text("/-!\n" + sentence + "\n-/\n", encoding="utf-8")
    return audit.check(path, KNOWN, specs, modules, cited)


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
