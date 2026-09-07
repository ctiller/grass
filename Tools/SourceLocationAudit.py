#!/usr/bin/env python3
"""Report tracked Lean sources that no build target and no audit covers.

`lakefile.toml` builds `Grass.+` and `Tests.+`. A `.lean` file anywhere else is not
elaborated, so `warningAsError = true` never sees it and a `sorry` in one does not
fail the build; and every audit in this directory scans `ROOT/Grass` and `ROOT/Tests`
only, so none of them sees it either.

**This is not hypothetical.** Two scratch probe files were swept into commits by a
`git add -A`, and one of them contained a `sorry`. Both were deleted a commit later
and neither ever failed a gate, because a repo-root `.lean` file is outside every
gate there is. Review found them in the history. There is precedent in this
repository for the same accident.

The check is a `git ls-files` filter, so it sees exactly what is committed rather
than what happens to be on disk — an untracked scratch file is nobody's problem and
is not reported.

**What it does not check.** It says nothing about whether a file *inside* the covered
trees is reachable: a module under `Grass/` that nothing imports is still elaborated
by the glob, which is what `Tools/AxiomAudit.lean`'s coverage check is for. And it
cannot tell a deliberately-unbuilt file from an accident, which is what `ALLOWED` is
for.

`--self-test` seeds each class and asserts the verdict.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Directories `lakefile.toml` builds, plus the ones a gate covers deliberately.
COVERED_PREFIXES = ("Grass/", "Tests/")

# Tracked Lean files outside those trees that are there on purpose.
ALLOWED = {
    # The two umbrella modules the `Grass.+` and `Tests.+` globs name.
    "Grass.lean",
    "Tests.lean",
    # The coverage audit, which arrived by merging main and is run the same way as
    # the axiom audit: `lake env lean Tools/CoverageAudit.lean` from the workflow,
    # not `lake build`. Same reason, different owner.
    "Tools/CoverageAudit.lean",
    # The axiom audit is run by `lake env lean`, not by `lake build`, because it is a
    # `run_cmd` over the whole environment rather than a library module.
    "Tools/AxiomAudit.lean",
    # The acceptance programs. They import modules that do not exist yet — an ISA,
    # an ABI, a platform — so they cannot be built, and `docs/MEMORY_IMPLEMENTATION_PLAN.md`
    # §4.2 records the consequence: they are prose to the build, and drift between
    # them and the reference fixtures is invisible to CI.
    "Spikes/",
}


def tracked_lean_files() -> list[str]:
    out = subprocess.run(
        ["git", "ls-files", "*.lean"], cwd=ROOT, capture_output=True, text=True, check=True
    )
    return [line.strip() for line in out.stdout.splitlines() if line.strip()]


def uncovered(paths: list[str]) -> list[str]:
    """The tracked Lean files no build target and no audit covers."""
    out: list[str] = []
    for path in paths:
        if path.startswith(COVERED_PREFIXES):
            continue
        if path in ALLOWED:
            continue
        if any(path.startswith(entry) for entry in ALLOWED if entry.endswith("/")):
            continue
        out.append(path)
    return sorted(out)


def inert_entries(paths: list[str]) -> list[str]:
    """The `ALLOWED` entries whose removal would change nothing.

    A leave-one-out over the real tracked file list. This gate had no such check while
    four siblings grew one; an entry here becomes inert when a file moves under a
    covered prefix or stops being tracked, which is good news and not a violation, so
    this reports rather than fails.

    `Spikes/` is a prefix rather than a path and `uncovered` treats it that way, so the
    sweep covers the prefix form too.
    """
    global ALLOWED
    original = set(ALLOWED)
    base = set(uncovered(paths))
    inert = []
    for entry in sorted(original):
        ALLOWED = original - {entry}
        if not set(uncovered(paths)) - base:
            inert.append(entry)
    ALLOWED = original
    return inert


def self_test() -> int:
    cases: list[tuple[str, list[str], list[str]]] = [
        ("a covered library file", ["Grass/Memory/State.lean"], []),
        ("a covered fixture", ["Tests/Op/FakeIsa.lean"], []),
        ("an umbrella module", ["Grass.lean"], []),
        ("a spike source", ["Spikes/1_Hello_World/Program.lean"], []),
        # The two that actually happened.
        ("a repo-root probe", ["ProbeB.lean"], ["ProbeB.lean"]),
        ("a probe in an uncovered directory", ["scratch/P1.lean"], ["scratch/P1.lean"]),
        # A near-miss: a directory whose name merely starts like a covered one.
        ("a lookalike directory", ["GrassOld/X.lean"], ["GrassOld/X.lean"]),
    ]
    failures = 0
    for label, paths, expected in cases:
        got = uncovered(paths)
        if got != expected:
            print(f"  SELF-TEST FAILED [{label}]: expected {expected}, got {got}")
            failures += 1
    # The `--inert` sweep, both directions, including the prefix form.
    global ALLOWED
    saved_allowed = set(ALLOWED)
    ALLOWED = {"Grass.lean", "nothing/tracked/here.lean"}
    if inert_entries(["Grass.lean"]) != ["nothing/tracked/here.lean"]:
        print("  SELF-TEST FAILED: the inert sweep does not separate a live entry "
              "from a dead one")
        failures += 1
    ALLOWED = {"Spikes/"}
    if inert_entries(["Spikes/1_Hello_World/Program.lean"]) != []:
        print("  SELF-TEST FAILED: a prefix entry that suppresses a real report is "
              "called inert")
        failures += 1
    ALLOWED = saved_allowed

    if failures:
        print(f"source location audit self-test: {failures} failure(s)")
        return 1
    print("source location audit self-test: all cases discriminate as documented")
    return 0


# The options this gate accepts. A misspelt flag used to be ignored: `--self-tset`
# and `--inertt` both ran the ordinary check and printed its success line at exit 0,
# so a reviewer sweeping a mode across the gates got a pass from a tool that never
# ran it. Review did exactly that in the round that found this, and one of the seven
# gates had no `--inert` implementation at all -- which is invisible when an unknown
# flag is a no-op and obvious the moment it is an error.
KNOWN_OPTIONS = {"--self-test", "--inert"}


def main() -> int:
    unknown = [arg for arg in sys.argv[1:] if arg not in KNOWN_OPTIONS]
    if unknown:
        print("unknown option(s): " + " ".join(unknown), file=sys.stderr)
        print("known: " + ", ".join(sorted(KNOWN_OPTIONS)), file=sys.stderr)
        return 2
    if "--self-test" in sys.argv:
        return self_test()
    paths = tracked_lean_files()
    if not paths:
        print("source location audit: git listed no Lean files", file=sys.stderr)
        return 1
    if "--inert" in sys.argv:
        inert = inert_entries(paths)
        if inert:
            print("allowlist entries that suppress nothing: " + ", ".join(inert))
            print("Delete them, or say why the entry is kept with no effect.")
        else:
            print("source location audit: every allowlist entry suppresses a report")
        return 0
    stray = uncovered(paths)
    if stray:
        print("\n".join(f"  {path}" for path in stray))
        print("\nsource location audit: tracked Lean sources outside every gate\n")
        print(
            f"{len(stray)} file(s) that `lake build` does not elaborate and no audit "
            "scans. Move them under Grass/ or Tests/, delete them, or add them to "
            "ALLOWED with the reason they are exempt."
        )
        return 1
    print(
        f"source location audit: all {len(paths)} tracked Lean sources are inside a "
        "build target or a recorded exemption"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
