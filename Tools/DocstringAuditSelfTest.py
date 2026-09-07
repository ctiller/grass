"""Falsifying tests for `Tools/DocstringAudit.py`.

A gate that is never tested against inputs it should *reject* is a gate that
can silently stop biting. This one already did once: an earlier version passed
a claim citing an invented theorem name, which is the exact defect its own
header gives as its reason for existing, and nothing noticed until a reviewer
constructed the case by hand.

So each case here is a sentence the tool must reach a stated verdict on, and
three of them are rejections. The specification corpus is the real one
read from `docs/`, because the point of two of these cases is *which* names
that corpus supplies -- nouns yes, proofs no -- and a synthetic corpus would
only test that the test agrees with itself.

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
# are about the *specification* half of resolution; the build half is already
# exercised every time the audit runs for real.
KNOWN = {"encode", "Bag", "cons_injective_right", "Prop", "Type", "Sort"}

CASES = [
    (
        "invented theorem name",
        "`encode` ensures every address has one encoding, as proved by "
        "`encodeMem_is_canonical_over_addresses`.",
        "look like declarations",
    ),
    (
        "theorem the specification plans but nothing proves",
        "Emission ensures the artifact is sound, as proved by "
        "`emitted_sound`.",
        "look like declarations",
    ),
    (
        "vocabulary the specification declares",
        "`Bag` ensures `ProcessSpec.Step` keeps multiplicity.",
        None,
    ),
    (
        "declaration in the build",
        "`cons_injective_right` ensures the remainder is unique.",
        None,
    ),
    (
        "claim naming nothing",
        "This ensures the encoding is unique.",
        "names no enforcing type",
    ),
    (
        "hedged claim",
        "This is intended to ensure the encoding is unique.",
        None,
    ),
]


def run_one(tmp: Path, sentence: str, specs, cited) -> list[str]:
    path = tmp / "Case.lean"
    path.write_text("/-!\n" + sentence + "\n-/\n", encoding="utf-8")
    return audit.check(path, KNOWN, specs, cited)


def main() -> int:
    specs = audit.specification_names()

    failures = []
    # The corpus itself must have the shape the design depends on.
    if "ProcessSpec.Step" not in specs:
        failures.append(
            "specification corpus lost `ProcessSpec.Step`; it is a structure "
            "field in docs/PROCESS.md and vocabulary resolution needs it")
    if "emitted_sound" in specs:
        failures.append(
            "specification corpus admitted `emitted_sound`; it is a planned "
            "theorem and only the build may supply proofs")

    with tempfile.TemporaryDirectory() as raw:
        tmp = Path(raw)
        for name, sentence, expected in CASES:
            cited: dict[str, str] = {}
            findings = run_one(tmp, sentence, specs, cited)
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
    rejects = sum(1 for _, _, expected in CASES if expected)
    print(f"docstring audit self-test: {len(CASES)} cases, "
          f"{rejects} rejections and {len(CASES) - rejects} "
          "acceptances as specified")
    return 0


if __name__ == "__main__":
    sys.exit(main())
