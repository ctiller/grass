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

**And it scans what it exempts.** Reporting a stray file was only half the job. Review
appended `theorem seededProbe : False := by sorry` to a tracked file under `Spikes/` and
all nine gates passed: `lake build` does not elaborate it, `AxiomAudit` walks the
elaborated environment, and the seven Python gates read `Grass/` and `Tests/`. The
exemption's reason — those files import modules that do not exist yet — justifies not
*building* them and does not justify not *reading* them, so every file `ALLOWED` covers
is now scanned for `sorry`, `axiom`, `native_decide` and `unsafe`, and a hit fails.
`False` provable inside a tracked tree is exactly the accident the paragraph above says
this file exists for; it was closed for the repo root and left open for the exemption.

**What it does not check.** It says nothing about whether a file *inside* the covered
trees is reachable: a module under `Grass/` that nothing imports is still elaborated
by the glob, which is what `Tools/AxiomAudit.lean`'s coverage check is for. And it
cannot tell a deliberately-unbuilt file from an accident, which is what `ALLOWED` is
for. The trust scan is lexical: it strips block comments, line comments and string
literals, and it cannot see a token a macro produces.

`--self-test` seeds each class and asserts the verdict.
"""

from __future__ import annotations

import re
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
    # The declaration-name printer `Tools/DocstringAudit.py` shells out to, run the
    # same way and arrived by merging main. Same reason, different owner.
    "Tools/DeclNames.lean",
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


# Single-line deliberately. `STRING` runs *first* now, so that a `/-` inside a
# string literal cannot open a comment in the scanner's eyes -- review wrote
# `def a := "/-"` above an `axiom` and below `def b := "-/"` and the whole run of
# real code between them was blanked. Running it first would be unsafe if it could
# span lines, because a stray quote inside a comment would then eat real code, so
# it cannot: a stray quote reaches the end of its own line and no further, and that
# line is a comment `BLOCK` or `LINE` blanks anyway.

# What may not appear in a Lean file no build elaborates. `Tools/AxiomAudit.lean`
# covers all of this inside the elaborated environment and cannot reach these files at
# all.
#
# **`sorryAx`, and every modifier that may precede a declaration.** The first version
# of this pattern was `\bsorry\b|\bnative_decide\b|^\s*axiom\s|^\s*unsafe\s`, and review
# walked past it with one keyword: `private axiom seededProbe : False` is valid Lean,
# elaborates, proves anything, and is not `^\s*axiom`. So were `protected`,
# `@[simp]`, and `Lean.sorryAx` -- which escapes `\bsorry\b` because `A` is a word
# character. The round that added this gate had written it to close exactly this hole
# and left four ways through, in its own allowlisted directory, with `False` provable
# under each. All eleven of review's probes -- the four that got through and the seven
# that did not -- are seeded in `self_test`.
#
# `axiom` and `unsafe` stay line-anchored because both are ordinary words; the anchor
# now steps over attributes and modifiers rather than requiring the keyword first.
MODIFIER = r"(?:private|protected|noncomputable|scoped|local|partial|opaque|unsafe)"
# **And after `in`, and at end of line.** The anchor above required the keyword to be
# the first token on its line after attributes and modifiers, and to be followed by
# whitespace *on that line*. Review walked past it three more ways: `open Nat in
# axiom seeded : False`, `set_option maxRecDepth 2000 in axiom ...`, and `axiom` at
# end of line with the signature wrapped to the next. All three elaborate and all
# three prove `False`. So the anchor admits a preceding `in` or `;` as well as line
# start, and ends at a word boundary rather than at whitespace.
#
# It stays anchored rather than becoming a bare `\baxiom\b`, because
# `Tools/AxiomAudit.lean` is itself an exempted file and is *about* axioms -- an
# unanchored pattern reports the gate that audits them.
UNTRUSTED = re.compile(
    r"\bsorry(?:Ax)?\b|\bnative_decide\b"
    r"|(?:^|\bin\s+|;)\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:" + MODIFIER + r"\s+)*(?:axiom|unsafe)\b",
    re.MULTILINE)


def blank(match: "re.Match[str]") -> str:
    """Replace a match with as many newlines as it spanned, keeping line numbers."""
    return chr(10) * match.group(0).count(chr(10))


# **A scanner rather than three regexes, because Lean nests block comments and a
# regex cannot.** What stood here was `/-.*?-/` non-greedy, `--.*?$`, and a
# single-line string, applied in an order two rounds argued about. Both remaining
# orders were wrong, and review demonstrated both:
#
#   * `/- outer /- inner -/ code -/` -- the non-greedy block closes at the first
#     `-/`, so `code` survives as source. A declaration referenced only inside a
#     comment counted as used, and a fixture nothing consumes went unreported.
#   * `-- a note mentioning /- something` -- `LINE` ran last, so a `/-` inside a
#     line comment opened a block for `BLOCK`, which swallowed every line down to
#     the next `-/` anywhere in the file. Review hid a real `MemoryState.alias`
#     call in `Grass/Memory/Loan.lean` behind one and all nine gates stayed green
#     -- the same demonstration that put `alias` in `DOORS`, reached through the
#     stripper instead of through the allowlist.
#
# The scanner tracks block-comment depth, opens a line comment on `--` only at
# depth zero and outside a string, and keeps a string literal from spanning lines.
# Every consumed character becomes a space and every newline is kept, so offsets
# and line numbers are the source's. Five gates share this; it is written out in
# each rather than imported, which is the same duplication the three patterns had.
#
# `QUOTE` and `BACKSLASH` are spelled with `chr` so that this file's own source
# carries neither where a reader might take it for the thing being matched.
QUOTE = chr(34)
APOSTROPHE = chr(39)
# Characters an apostrophe may follow as a *prime* on a name rather than opening a
# char literal. Lean allows `h'`, `foo''` and `x?'`.
PRIMEABLE = frozenset(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_!?" + chr(39))
BACKSLASH = chr(92)


def strip(source: str) -> str:
    """Blank comments and string literals, keeping the line structure.

    Line numbers have to survive: a report that points at the wrong line is the defect
    `Tools/CitationAudit.py` and `Tools/DoorAudit.py` were each found with.

    Strings are blanked **before** comments, which is the opposite of the order the
    sibling tools use and is deliberate: this one is a trust gate, so the failure that
    matters is blanking too much rather than too little, and a `/-` inside a string
    literal blanked every line to the next `-/`.
    """
    out: list[str] = []
    depth = 0
    in_string = False
    in_line_comment = False
    index = 0
    size = len(source)
    while index < size:
        char = source[index]
        if char == chr(10):
            out.append(chr(10))
            in_line_comment = False
            # A string left open at a newline is a lexical error in the source
            # rather than licence to blank the rest of the file. Reached only when
            # the newline is *not* part of a string gap; a gap is consumed by the
            # escape branch below, which keeps `in_string` set.
            in_string = False
            index += 1
            continue
        if in_line_comment:
            out.append(chr(32))
            index += 1
            continue
        if in_string:
            if char == BACKSLASH and index + 1 < size:
                # A **string gap**: a backslash immediately before a newline
                # continues the literal onto the next line. Lean 4 has these, and
                # the comment above this branch used to say it did not. Emitting
                # two spaces here consumed the newline: total length was preserved,
                # so the advertised invariant appeared to hold, while the line count
                # dropped and every finding after the gap was reported one line
                # early. Review measured it -- a door call on line 195 reported as
                # 194, with a gap-free control on 191 reported correctly.
                #
                # The newline is emitted and `in_string` stays set, because the
                # literal really does continue.
                # CRLF first, and it is the half that is unsafe rather than
                # merely wrong. On a CRLF checkout the escape ate the
                # backslash and the CR, the LF then hit the top-of-loop reset,
                # and `in_string` cleared **mid-string** -- so the
                # continuation line was scanned as source while the string's
                # own tail was not, which is the hiding direction. What holds
                # it off today is `.gitattributes` (`* text=auto eol=lf`),
                # which no gate consults, against a repo-local
                # `core.autocrlf=true`.
                if (index + 2 < size and source[index + 1] == chr(13)
                        and source[index + 2] == chr(10)):
                    out.append(chr(32))
                    out.append(chr(13))
                    out.append(chr(10))
                    index += 3
                    continue
                if source[index + 1] == chr(10):
                    out.append(chr(32))
                    out.append(chr(10))
                    index += 2
                    continue
                out.append(chr(32) * 2)
                index += 2
                continue
            out.append(chr(32))
            if char == QUOTE:
                in_string = False
            index += 1
            continue
        if depth > 0:
            if source.startswith(chr(47) + chr(45), index):
                depth += 1
                out.append(chr(32) * 2)
                index += 2
                continue
            if source.startswith(chr(45) + chr(47), index):
                depth -= 1
                out.append(chr(32) * 2)
                index += 2
                continue
            out.append(chr(32))
            index += 1
            continue
        if source.startswith(chr(47) + chr(45), index):
            depth = 1
            out.append(chr(32) * 2)
            index += 2
            continue
        if source.startswith(chr(45) * 2, index):
            in_line_comment = True
            out.append(chr(32) * 2)
            index += 2
            continue
        # A char literal, before the quote branch, because `'"'` holds a bare
        # quote and opened a string that blanked the rest of the line -- review put
        # two door calls on one line either side of one and watched the second
        # disappear. Only when the apostrophe cannot be a prime on an identifier:
        # `h'` and `foo'` are ordinary Lean names and must not start a literal.
        if char == APOSTROPHE and not (out and out[-1][-1:] in PRIMEABLE):
            if (index + 3 < size and source[index + 1] == BACKSLASH
                    and source[index + 3] == APOSTROPHE):
                out.append(chr(32) * 4)
                index += 4
                continue
            if index + 2 < size and source[index + 2] == APOSTROPHE:
                out.append(chr(32) * 3)
                index += 3
                continue
        if char == QUOTE:
            in_string = True
            out.append(chr(32))
            index += 1
            continue
        out.append(char)
        index += 1
    return "".join(out)


def untrusted(paths: list[str]) -> list[str]:
    """Trust tokens in tracked Lean files that no build target elaborates.

    Only the exempted ones: a file under `Grass/` or `Tests/` is elaborated with
    `warningAsError = true`, so `sorry` fails the build there, and `Tools/AxiomAudit.lean`
    covers the rest of the vocabulary. These files have neither.
    """
    out: list[str] = []
    for path in paths:
        if path.startswith(COVERED_PREFIXES):
            continue
        covered = path in ALLOWED or any(
            path.startswith(entry) for entry in ALLOWED if entry.endswith("/"))
        if not covered:
            continue
        try:
            text = (ROOT / path).read_text(encoding="utf-8")
        except OSError:
            continue
        for number, line in enumerate(strip(text).splitlines(), start=1):
            match = UNTRUSTED.search(line)
            if match:
                out.append(
                    f"  {path}:{number}: `{match.group(0).strip()}` in a file no build "
                    "target elaborates")
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
    # The trust scan, seeded case by case against the real exempted-file machinery. A
    # probe is written to a temporary path under an exempted directory and removed, so
    # each case is exercised without a file ever being committed.
    #
    # **The first version of this block seeded two cases and the scan had four holes.**
    # It asserted that a bare `sorry` is reported and that `sorry` in a comment or a
    # string is not, which is exactly the pair of cases the pattern was written from --
    # so it tested the author's model of the pattern rather than the pattern. Review
    # walked past the gate four ways, and all eleven of its probes are below with the
    # negatives beside them. A trust gate's self-test wants the cases somebody tried to
    # get through it, not the cases it was built from.
    quote = chr(34)
    trust_cases: list[tuple[str, bool]] = [
        ("axiom seeded : False", True),
        # The four that got through.
        ("private axiom seeded : False", True),
        # And review's three from the round after, which the anchor above also let
        # through: a preceding `open ... in`, a preceding `set_option ... in`, and
        # the keyword at end of line with the signature wrapped.
        ("open Nat in axiom seeded : False", True),
        ("set_option maxRecDepth 2000 in axiom seeded : False", True),
        ("axiom" + chr(10) + "  seeded : False", True),
        # A word merely beginning with the keyword is not the keyword.
        ("theorem t : x = axiomatic := rfl", False),
        ("protected axiom seeded : False", True),
        ("@[simp] axiom seeded : False", True),
        ("private unsafe def f : Nat := 0", True),
        # `sorryAx` is what `sorry` elaborates to, and `A` is a word character.
        ("theorem p : False := Lean.sorryAx False false", True),
        # A `/-` inside a string opened a comment and blanked the lines between.
        ("def a := " + quote + "/-" + quote + chr(10) + "axiom seeded : False" + chr(10)
         + "def b := " + quote + "-/" + quote, True),
        # The seven that did not.
        ("theorem p : False := by sorry", True),
        ("unsafe def f : Nat := 0", True),
        ("/- outer /- inner -/ -/" + chr(10) + "axiom seeded : False", True),
        ("example : True := by native_decide", True),
        # And what it must stay quiet on.
        ("/-- a docstring mentioning sorry and axiom -/" + chr(10) + "def f := 1", False),
        ("-- a line comment mentioning sorry and axiom", False),
        ("def f := " + quote + "sorry" + quote, False),
        ("def notAnAxiomAtAll := 1", False),
    ]
    probe = ROOT / "Spikes" / "__self_test_probe.lean"
    try:
        for text, should_report in trust_cases:
            probe.write_text(text + chr(10), encoding="utf-8")
            if bool(untrusted(["Spikes/__self_test_probe.lean"])) != should_report:
                want = "reported" if should_report else "not reported"
                first = text.splitlines()[0]
                print(f"  SELF-TEST FAILED [trust scan]: expected {want} for {first!r}")
                failures += 1
        # And the report names the file and the line, which is what a reader chases.
        probe.write_text("def f := 1" + chr(10) + "axiom seeded : False" + chr(10),
                         encoding="utf-8")
        hits = untrusted(["Spikes/__self_test_probe.lean"])
        if not hits or "Spikes/__self_test_probe.lean:2" not in hits[0]:
            print("  SELF-TEST FAILED [trust scan]: the reported line number is wrong")
            failures += 1
    finally:
        if probe.exists():
            probe.unlink()
    # A covered file is not scanned here, because `lake build` already fails on it.
    if untrusted(["Grass/Memory/State.lean"]):
        print("  SELF-TEST FAILED: a file inside a build target is scanned by the trust "
              "check, which is the build's job")
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

    # The shared scanner, both shapes review defeated it with. Neither had a
    # case here: `BACKSLASH` appeared only in this file's own comment, constant
    # and single use, and no seed contained an apostrophe -- so both defects were
    # invisible to CI while the gate printed its success line.
    #
    # A **string gap** -- a backslash immediately before a newline -- continues a
    # Lean literal. The escape branch used to consume the newline, preserving
    # total length while dropping a line, so every finding below a gap was
    # reported one line early. Length is the invariant the docstring advertises
    # and it is the weaker one; the line count is what a report cites.
    gapped = ("def s : String :=" + chr(10) + "  " + chr(34) + "a" + chr(92) + chr(10)
               + "  b" + chr(34) + chr(10) + "def afterGap := 1" + chr(10))
    if strip(gapped).count(chr(10)) != gapped.count(chr(10)):
        print("  SELF-TEST FAILED: a string gap loses a line, shifting every "
              "reported line number after it")
        failures += 1

    # The same gap with **CRLF** endings, which is the half that hides source
    # rather than merely shifting a number. The escape ate the backslash and the
    # CR; the LF then hit the top-of-loop reset and cleared `in_string`
    # mid-literal, so the string's own tail was scanned as source. Held off only
    # by `.gitattributes`, which no gate consults.
    crlf = ("def s : String :=" + chr(13) + chr(10) + "  " + chr(34) + "a" + chr(92) + chr(13) + chr(10)
            + "  MemoryState.alias" + chr(34) + chr(13) + chr(10))
    if "MemoryState.alias" in strip(crlf):
        print("  SELF-TEST FAILED: a CRLF string gap exposes the string's tail "
              "as source")
        failures += 1
    if strip(crlf).count(chr(10)) != crlf.count(chr(10)):
        print("  SELF-TEST FAILED: a CRLF string gap loses a line")
        failures += 1

    # A **char literal** holding a quote must not open a string and blank the
    # rest of the line. Review put two door calls either side of one and watched
    # the second disappear.
    charlit = "def p := (alpha, " + chr(39) + chr(34) + chr(39) + ", omega)" + chr(10)
    if "omega" not in strip(charlit):
        print("  SELF-TEST FAILED: a char literal holding a quote hides the "
              "rest of its line")
        failures += 1

    # Controls, so neither repair is a blanket disabling. A real string literal
    # is still blanked, and an apostrophe that is a *prime* on a name -- `h'`,
    # ordinary Lean -- does not start a literal and eat what follows.
    if "hidden" in strip("def s := " + chr(34) + "hidden" + chr(34) + chr(10)):
        print("  SELF-TEST FAILED: a real string literal is no longer blanked")
        failures += 1
    if "visible" not in strip("theorem h" + chr(39) + " : True := visible" + chr(10)):
        print("  SELF-TEST FAILED: a primed identifier swallows what follows it")
        failures += 1

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
    tainted = untrusted(paths)
    if tainted:
        print(chr(10).join(tainted))
        print(chr(10) + "source location audit: an unelaborated file carries a trust "
              "token" + chr(10))
        print(
            f"{len(tainted)} occurrence(s). These files are exempt from `lake build`, so "
            "nothing else in the tree will ever report this."
        )
        return 1
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
        "build target or a recorded exemption, and no exempted file carries a trust token"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
