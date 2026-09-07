#!/usr/bin/env python3
"""Report inductive constructors nothing outside their own declaration builds.

`docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.4.1 asks for this in its own words:

    Nothing enforces that every `AuthorityState` constructor stays reachable. Four
    fixtures exhibit one each. A fifth constructor, or a change that made one
    unreachable, would be caught by a reader and not by a gate.

That gap is not hypothetical. `AuthorityState` carried `sharedImmutable`,
`unavailable` and `atomicShared` with nothing building any of them, so every theorem
about them held of a term no state could reach — which reads as coverage and is not.
Two were made reachable and one was deleted; the same thing can happen again, and
`Tools/ConsultedAudit.py` cannot see it, because it scans structure fields and this
is about sum constructors.

**What this checks, exactly.** For each `inductive T` under `Grass/`, within `SCOPE`,, it collects the
constructor names on `| ctor` lines. It then searches the comment- and
string-stripped sources of `Grass/` and `Tests/` for a construction site outside the
declaration itself: either the qualified `T.ctor`, or a bare `.ctor` that is not in a
match-arm position. A constructor with none is reported.

**What it does not check**, stated because two tools in this directory have been
corrected for advertising a stronger reading:

- **It covers this branch's tree, not the repository.** `SCOPE` below names the
  subtrees, which are the ones this branch had before merging `origin/main`:
  `Grass/{Certificate,Core,Memory,Obligation,Op,Resource,Semantics,Std,Trust,
  Verify}` and `Tests/{Foundation,Memory,Op,Resource,Std}`. `Grass/ISA`,
  `Grass/ABI`, `Grass/Process` and their fixtures are **not covered by this gate
  or by anything of this kind** — not because they are clean, but because
  reporting a declaration as unread is a judgement only that code's owner can
  make. Four of the subtrees that *are* covered belong to other owners too; their
  findings are allowlisted with the reason and reported rather than decided here.

  The comment above `SCOPE` used to say "the honest statement of coverage is in
  the module docstring", and there was no such statement in any of the four
  docstrings. A sentence that delegates to text nobody wrote is worse than no
  sentence: it reads as a promise kept.

- Dot notation is namespace-blind, exactly as in `ConsultedAudit.py`. Two inductives
  with a constructor of the same name are indistinguishable, so building one
  satisfies the other. Lean would have to be elaborated to do better.
- It cannot tell a construction in live code from one in dead code, nor "built" from
  "built only by a fixture that asserts nothing about it".
- It cannot see a constructor produced by a generic function returning `T`, or by
  `deriving`, or by a `default` field value spelled without the constructor's name.
- Match arms are excluded by a heuristic: a `.ctor` is a *pattern* if it is followed
  by `=>`, or preceded on the same line by a `|` with no `=>` between them. A
  construction written to look like that is missed, and a pattern written across
  lines may be counted as a construction — a false negative and a false positive
  respectively. The `|`-with-no-`=>` refinement is not cosmetic: without it, a
  constructor built on the value side of an arm was reported as unbuilt.
- **A constructor named in a theorem's own statement counts as built.** `theorem t
  (h : a.kind = .fence) : …` reads exactly like a construction, and it is one — the
  term `.fence` is built, to be compared against. What the tool cannot tell is
  whether anything *reachable* produces it. That is the shape it was written to
  catch, so this is the blind spot that matters most: review found
  `MemoryEvent.EventKind.fence` unconstructible by any producer, with its only
  occurrence inside a theorem about it, and this tool silent. Reaching further needs
  elaboration, not a regex.
- It cannot see a constructor of an inductive whose constructors are written flush
  left (`inductive T where` then `| a` at column zero, which is legal). That shape
  does not occur in `Grass/` today; it is one reformat away, and the scanner treats
  the `|` line as the end of the declaration.

So a clean run means every constructor's name appears somewhere that looks like a
construction. It is one cheap net over a defect this layer has hit three times in one
type, and it under-reports by design.

The allowlist is where "declared deliberately without a builder" is recorded, with a
reason per entry.

`--self-test` seeds each class this file claims to catch and each near-miss it must
stay quiet on. Run it after changing the scanner.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# **Scope: the tree this branch had before merging main.**
#
# Merging `origin/main` put three other owners' trees under these globs -- `Grass/ISA`,
# `Grass/ABI`, `Grass/Process` and their fixtures -- and this gate immediately reported
# findings in them. Every one may be true and none is this branch's to judge: an
# allowlist entry here records that *somebody read the corpus and decided*, and nobody
# on this branch has read theirs.
#
# **The first version of this list was written by hand and was wrong in both
# directions.** It named eight subtrees from memory and dropped three that were in this
# branch's own tree before the merge -- `Grass/Certificate.lean`, `Grass/Verify/` and
# `Tests/Foundation.lean` -- which cost one live finding and made two allowlist entries
# read as inert. A scope written from what the author remembered owning is the same
# defect as a count written from reading rather than running. It is the pre-merge tree
# now, which is a fact rather than a recollection: `git ls-tree b9d4200 Grass/ Tests/`.
#
# Widening it is one edit, and the module docstring says what is not covered.
SCOPE = ("Certificate", "Core", "Memory", "Obligation", "Op", "Resource", "Semantics",
         "Std", "Trust", "Verify", "Foundation")


def in_scope(path) -> bool:
    """Whether a path lies in one of `SCOPE`'s subtrees.

    Relative to `ROOT`, not by scanning absolute components for the first `Grass` or
    `Tests`. The scanning form had two failures review demonstrated: a path under a
    top-level directory this branch has not created yet fell out silently, and a
    checkout directory *named* `Grass` -- which is what this project is called -- made
    the repository root the first match and put every file out of scope.
    """
    try:
        parts = path.resolve().relative_to(ROOT).parts
    except ValueError:
        # Outside the repository: not this gate's business, and not silently in scope.
        return False
    if len(parts) < 2 or parts[0] not in ("Grass", "Tests"):
        return True
    return parts[1].removesuffix(".lean") in SCOPE


def scope_is_covered(paths, trees=("Grass", "Tests")) -> list[str]:
    """Report if the scope filter has emptied the file list or lost a known subtree.

    **`SCOPE` was a coverage claim with nothing behind it.** Review dropped one token
    from it and three gates went silent for this layer while printing their success
    lines; no self-test touched `in_scope`, because every self-test writes probe files
    into a temporary directory and calls the scanner directly, so the path filter is
    never on the tested path. Only total emptiness was guarded, and only in three of the
    six gates.

    A floor rather than an emptiness check, in the shape
    `Tools/DocstringAudit.py`'s `declaration_names` already uses (`if len(known) <
    1000`): every subtree named in `SCOPE` that exists on disk must contribute at
    least one file.

    **What this cannot catch, stated because the first version of this paragraph
    claimed it could.** It derives its expectation from `SCOPE`, so deleting a token
    from `SCOPE` deletes the check for that subtree along with it -- exactly the
    attack it was written against, and it passes. What it does catch is the globs or
    `in_scope` breaking under a `SCOPE` that still names the subtree, which is the
    other half and the one no gate had.

    The authority on `SCOPE`'s *contents* is `self_test`, which asserts membership
    against four hard-coded paths rather than against `SCOPE`. CI runs every gate's
    self-test before the gate, so a narrowed `SCOPE` fails there. A check derived
    from the thing it is checking is not a check, and saying which half is which is
    the whole content of this paragraph.

    `trees` is which of `Grass/` and `Tests/` this gate's list actually covers;
    asking about the other one reports every subtree of it as unreached, which
    is the first thing this check did.
    """
    missing = []
    for name in SCOPE:
        for tree in trees:
            candidate = ROOT / tree / name
            if not (candidate.is_dir() or candidate.with_suffix(".lean").is_file()):
                continue
            prefix = (tree, name)
            if not any(
                    p.resolve().relative_to(ROOT).parts[:2] in
                    (prefix, (tree, name + ".lean"))
                    for p in paths):
                missing.append(f"  {tree}/{name}: in SCOPE, on disk, and no file "
                               "reached the scan")
    return missing


DECLARED_IN = [p for p in sorted((ROOT / "Grass").rglob("*.lean")) if in_scope(p)]
# Unscoped, both trees, for the reason `Tools/ConsultedAudit.py` states at its own
# `READERS_IN`: this was `DECLARED_IN + Tests/`, so a constructor built only from
# `Grass/ISA` was reported unbuilt while one built only from `Tests/ISA` was not.
# `SCOPE` governs what this gate adjudicates, never where it looks for a use.
BUILDERS_IN = (sorted((ROOT / "Grass").rglob("*.lean"))
               + sorted((ROOT / "Tests").rglob("*.lean")))

INDUCTIVE = re.compile(r"^\s*(?:private\s+|protected\s+)?inductive\s+([A-Za-z_][A-Za-z0-9_.']*)")
CONSTRUCTOR = re.compile(r"\|\s*([A-Za-z][A-Za-z0-9_']*)")
def blank(match: "re.Match[str]") -> str:
    """Replace a match with as many newlines as it spanned, keeping line numbers."""
    return chr(10) * match.group(0).count(chr(10))

# Comments and string literals, blanked so line numbers survive.
#
# **These three patterns and this order are the same in every gate in this
# directory, and were not.** Review found `SourceLocationAudit.py` blanking real code
# because a `/-` inside a string literal opened a comment; that was repaired there and
# the four siblings kept the defect, mirrored -- they ran `STRING` before `LINE`, so a
# `" in a *line comment* opened a string and everything down to the next quote was
# erased. Review appended a real door call between two such comments and every gate
# stayed green.
#
# The order is `STRING`, then `BLOCK`, then `LINE`, and `STRING` cannot span lines.
# That is the only arrangement where neither construct can swallow the other: a quote
# inside a comment reaches the end of its own line and no further, and that line is a
# comment the next two patterns blank anyway. `blank` rather than deletion, because a
# report that points at the wrong line is the defect this file's sibling was found
# with twice.

# Constructors carried without a builder, as `Inductive.constructor` pairs. Every
# entry says why.
#
# **Pairs, not bare names.** The first version was a set of bare constructor names, so
# an entry exempted *any* constructor of that name on *any* inductive — a second
# namespace-blindness, distinct from the one the scan has and worse, because it grows
# silently as the tree does. Review demonstrated a fresh unbuilt constructor going
# unreported because an unrelated type had a constructor of the same name, and found
# eight of the twenty-one entries inert.
ALLOWED = {
    # Portable ordering and scope names section 7.1 fixes. A profile picks the ones
    # its target has; the model owes all of them.
    #
    # Two groups stood here and are gone, along with five entries from this one:
    # "vocabulary an ISA or profile supplies" (`Address.symbolic`,
    # `AddressRepr.symbolic`, the three `profileSpecific`) and "terminal and
    # lifecycle vocabulary whose consumers are later milestones" (both
    # `Restartability` constructors). Every one of the twelve suppressed nothing,
    # and five of them were flatly contradicted by the tree: `Restartability`'s two
    # are a struct field default in `Grass/Memory/Access.lean` and a fixture,
    # `Atomicity.nonAtomic` is a field default in `Grass/Memory/Ordering.lean`,
    # `Address.symbolic` is built in `Tests/Memory/WellFormedClauses.lean` and
    # `AddressRepr.symbolic` in `Grass/Memory/AddressSpace.lean`. The rest were
    # silenced by this tool's own same-name blindness -- `MemoryScope.system` by an
    # unrelated `system` component, two `profileSpecific` by the third.
    #
    # `--inert` exists now, so this cannot rot back the way it did. The preamble
    # above records the same sweep being run once already, by hand, and finding
    # eight of twenty-one; the entries that grew back are why a hand sweep is not
    # enough.
    "MemoryScope.process",
    "MemoryScope.device",
    # --- Declared ahead of the milestone that builds them. Being listed here is not
    # --- "this is fine": it is the record that someone read the plan and decided,
    # --- and the reason differs per entry.
    #
    # Requirement vocabulary from another owner's modules, which arrived here by
    # merging main. `RequirementKind` declares **twelve** constructors and nothing in
    # the tree builds one; `DemandFamily.kind`'s own docstring calls it "exact metadata
    # only", so unbuilt is consistent with its intent -- a demand provider supplies
    # the kind, and no provider exists yet. Listed rather than silenced, and reported to
    # that owner: whether a twelve-name vocabulary with no producer and no consumer is
    # the right shape is their decision, not this branch's.
    #
    # This said "ten" and "a ten-name **closed** vocabulary", and both halves were
    # written from the ten entries below rather than from the type. The other two,
    # `memory` and `artifact`, pass this gate only through its own documented same-name
    # blindness -- `.memory` matches `state.memory` on hundreds of lines -- so they are
    # not listed here and cannot be, since an entry for a name this scanner is blind to
    # reads as a judgement somebody made and is not one. And the vocabulary is not
    # closed: `extension (owner kind : StableId)` is an open escape, which is the whole
    # subject of the `g-design:13` ruling that module cites. **A count written from an
    # allowlist counts the allowlist.**
    # --- Four entries left this list when the merge widened the tree, and the sweep
    # --- that found `ConsultedAudit`'s did not look here -- a repair applied to the
    # --- instance, in the commit whose own subject is same-name blindness.
    #
    # --- `RequirementKind.progress`, `RequirementOrigin.external` and
    # --- `Disposition.transferred` are all still unbuilt. They read as built because
    # --- `correct.progress ()`, `.external` throughout `Grass/Process/Vocabulary.lean`
    # --- and `classification.transferred.card` match the short names.
    # --- `Disposition.transferred` is the one that costs something: §3's terminal
    # --- disposition vocabulary being unconstructed is a gap §4.4.1 records, and this
    # --- gate can no longer state it.
    #
    # --- `RequirementKind.artifact` joins them, one round after being added here
    # --- because a scanner repair had made it visible. It is invisible again for the
    # --- older reason, which is what an entry added on the strength of one repair and
    # --- undone by the next looks like.
    "RequirementKind.functional",
    "RequirementKind.safety",
    "RequirementKind.concurrency",
    "RequirementKind.termination",
    "RequirementKind.resource",
    "RequirementKind.obligation",
    "RequirementKind.diagnostic",
    "RequirementKind.applicability",
    "RequirementKind.extension",
    # `artifact` joins the list rather than being reported, and its arrival is this
    # tool working rather than the tree changing: the round that stopped the
    # declaration walk from skipping a line when a docstring shares it, and stopped a
    # quote in a comment from blanking real code, is what made this constructor visible.
    # `memory` is still hidden by the documented same-name blindness -- `.memory`
    # matches `state.memory` on hundreds of lines -- so it is not listed, because an
    # entry for a name this scanner cannot see records a judgement nobody made.
    "RequirementOrigin.prior",
    # `EventKind.control` stood here too, on the reason that control flow is the
    # ISA owner's and the causal graph is M8's -- accurate about the *transition*,
    # which still mints none. It went the way its twin `EventKind.fence` went one
    # round earlier and for the same reason: `Tests/Memory/EventClauses.lean` mints
    # one now.
    #
    # It had to. `MemoryEvent.WellFormed`'s location clause says "a fence or control
    # event has no location", and every fixture deciding it was a fence, so review
    # narrowed the clause's guard from `touchesMemory = false` to `kind = .fence` --
    # co-editing the `Decidable` instance, `sealClauses` and the producer's
    # discharge -- and the whole tree stayed green with a control event carrying an
    # eight-byte range admitted by the seal.
    #
    # That is a second cost of an entry here, beyond the dead-allowlist one this
    # tool reports: **a constructor nothing builds is a constructor every clause
    # about it is undecided for.** An entry recording "a later milestone owns the
    # producer" is also recording that any rule quantifying over the type is
    # exercised on a proper subset of it.
    # `EventKind.fence` stood here on the same ground and is gone. The reason was
    # accurate and remains recorded in `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2 —
    # nothing in the *transition* can mint one, because `kindOf` yields only `read`,
    # `write` and `readModifyWrite` and an intent that neither reads nor writes is
    # refused by `WellFormedIn.notInert`, so §7.4's "release establishes the profile's
    # causal edge" has no event to carry it. But `Tests/Memory/EventClauses.lean` mints
    # three fence events directly, to isolate the seal clauses about an event that
    # touches no memory, so the entry had stopped suppressing anything.
    #
    # It was the first entry this file's own `--inert` check ever reported, and it
    # reported it only after the check was repaired: for its whole life the check
    # matched entry names inside backticks against a report format that has no
    # backticks, so it printed every entry in the list every run.
    # `docs/OBLIGATIONS.md` section 3 requires every obligation at a terminal edge to
    # receive a disposition. M5 owns terminal accounting and does not exist, so this
    # one is named and unbuilt. It said "these two" and the entry beside it,
    # `Disposition.transferred`, was deleted by the commit that wrote the sentence
    # -- a count broken by the change whose own subject was allowlist accuracy.
    #
    # An earlier version of this comment added "`Spikes/1_Hello_World` needs both",
    # and review checked: that directory holds `Program.lean` and `Spec.lean` and
    # neither mentions a disposition or an obligation at all. A false reason on an
    # allowlist entry is worse than none, because it reads as an argument somebody
    # made. The true reason is the first two sentences.
    #
    # The other four `Disposition` constructors are *not* listed here and are just
    # as unbuilt: three appear only in match arms and in three one-line simp theorems,
    # which this tool counts as construction. That is the blind spot its own docstring
    # calls the one that matters most, and review demonstrated it by deleting the
    # three theorems and watching all three constructors get reported.
    "Disposition.teardownAdopted",
    # The resource layer is built ahead of its consumers, which arrive at M7 and M9.
    # `Tools/ConsultedAudit.py` records the same thing about its fields.
    "ResourceLifecyclePolicy.affineTransfer",
    "ResourceLifecyclePolicy.sharedOnce",
    "ResourceLifecyclePolicy.phaseExclusive",
    "ResourceLifecyclePolicy.scopedRelease",
    "ResourceExhaustionPolicy.reject",
    "ResourceExhaustionPolicy.backpressure",
    "ResourceExhaustionPolicy.fail",
}


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


def scannable(text: str) -> str:
    """Strip comments and string literals, as `ConsultedAudit.py` does.

    Prose naming a constructor is not a construction of it, and this file's own
    docstring names several.
    """
    out: list[str] = []
    depth = 0
    in_string = False
    in_line_comment = False
    index = 0
    size = len(text)
    while index < size:
        char = text[index]
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
                if (index + 2 < size and text[index + 1] == chr(13)
                        and text[index + 2] == chr(10)):
                    out.append(chr(32))
                    out.append(chr(13))
                    out.append(chr(10))
                    index += 3
                    continue
                if text[index + 1] == chr(10):
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
            if text.startswith(chr(47) + chr(45), index):
                depth += 1
                out.append(chr(32) * 2)
                index += 2
                continue
            if text.startswith(chr(45) + chr(47), index):
                depth -= 1
                out.append(chr(32) * 2)
                index += 2
                continue
            out.append(chr(32))
            index += 1
            continue
        if text.startswith(chr(47) + chr(45), index):
            depth = 1
            out.append(chr(32) * 2)
            index += 2
            continue
        if text.startswith(chr(45) * 2, index):
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
            if (index + 3 < size and text[index + 1] == BACKSLASH
                    and text[index + 3] == APOSTROPHE):
                out.append(chr(32) * 4)
                index += 4
                continue
            if index + 2 < size and text[index + 2] == APOSTROPHE:
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


def constructors_in(text: str) -> list[tuple[str, str, int]]:
    """Yield (inductive, constructor, line) for every constructor in one source.

    **Comments are blanked before the walk rather than skipped during it.** The hand-
    rolled skipper this replaces discarded any line whose first token opened a comment,
    so a declaration sharing a line with its own docstring -- `/-- doc -/ | reclaimed`,
    which is legal Lean -- was not merely unreported but never examined. Review seeded
    an inductive written that way and an unread structure field written that way, and
    every gate stayed green. `BLOCK.sub(blank, ...)` leaves whatever follows the `-/`
    on the line and keeps the line number, which is what the walk needs and what the
    skipper could not give it.

    **Every constructor on the line, not the first.** `| reclaimed | abandoned` is legal
    and the second was invisible, as was the whole of `inductive Foo where | a | b`,
    because the walk matched at most one constructor per line and treated the
    `inductive` line as carrying none. And the name pattern required a lower-case
    initial, so a capitalised constructor was not a constructor to this tool -- three
    shapes review seeded, all silent, in the gate whose subject is a constructor nothing
    builds.
    """
    out: list[tuple[str, str, int]] = []
    current: str | None = None
    for number, line in enumerate(scannable(text).splitlines(), 1):
        stripped = line.strip()
        match = INDUCTIVE.match(line)
        if match:
            current = match.group(1)
            # `inductive Foo where | a | b` declares two of them on this line.
            for name in CONSTRUCTOR.findall(line[match.end():]):
                out.append((current, name, number))
            continue
        if current is None:
            continue
        found = CONSTRUCTOR.findall(line)
        if found and line.lstrip().startswith("|"):
            for name in found:
                out.append((current, name, number))
            continue
        # A constructor line ends nothing. Testing for the end *first* meant an
        # inductive whose constructors are flush left — legal Lean — had every one of
        # them skipped and the tool printed a clean run.
        if stripped.startswith("deriving") or (stripped and not line.startswith(" ")):
            current = None
    return out


def builds(body: str, inductive: str, constructor: str) -> bool:
    """Whether `body` looks like it constructs `Inductive.constructor` somewhere.

    A qualified mention always counts. A bare `.ctor` counts unless it is in a
    match-arm *pattern* position: followed by `=>`, or preceded on the same line by a
    `|` with no `=>` between them.
    """
    if re.search(r"\b%s\.%s\b" % (re.escape(inductive.split(".")[-1]),
                                  re.escape(constructor)), body):
        return True
    for line in body.splitlines():
        for match in re.finditer(r"\.%s\b" % re.escape(constructor), line):
            before = line[: match.start()]
            after = line[match.end() : match.end() + 6]
            if "=>" in after:
                continue
            # A `|` earlier on the line makes this a pattern only if no `=>` has
            # intervened. `| some space => if p then [] else [.ctor x]` builds on the
            # value side of an arm, and a first version of this rule called it a
            # pattern and reported the constructor as unbuilt.
            bar = before.rfind("|")
            if bar != -1 and "=>" not in before[bar:]:
                continue
            return True
    return False


def analyse(raw: dict[str, str], builders: dict[str, str] | None = None) -> list[str]:
    """Report `path:line: Inductive.ctor` for every constructor nothing builds."""
    corpus = {name: scannable(text) for name, text in (builders or raw).items()}
    unbuilt: list[str] = []
    for name, text in raw.items():
        declaring = scannable(text)
        for inductive, constructor, line in constructors_in(text):
            if f"{inductive.split('.')[-1]}.{constructor}" in ALLOWED:
                continue
            found = False
            for other, body in corpus.items():
                # The declaration's own file counts only outside the `inductive`
                # block, which `constructors_in` already located; a `| ctor` line is
                # not a construction, and `builds` skips it for the leading `|`.
                if builds(body if other != name else declaring, inductive, constructor):
                    found = True
                    break
            if not found:
                unbuilt.append(
                    f"  {name}:{line}: {inductive}.{constructor} is declared and "
                    "nothing appears to build it"
                )
    return unbuilt


def inert_entries(declared: dict[str, str], builders: dict[str, str]) -> list[str]:
    """The `ALLOWED` entries whose removal would change nothing.

    A real leave-one-out, which is what this check was supposed to be from the day it
    landed. It was not. It emptied the allowlist, ran `analyse`, joined the reports and
    looked for each entry inside backticks -- and this tool's report format has no
    backticks, so nothing was ever found and every entry was declared inert. All
    twenty-five of them, every run, while each was suppressing exactly one report.

    The comment that stood here argued for exact-name matching over a substring of the
    joined report, on the ground that an entry which is a strict prefix of another
    reported name would read as live. That was a true observation about substring
    matching. The version it replaced *worked*, because the plain report text contains
    the names; the version it introduced matched a delimiter the format does not use.
    A check that reports everything is a check that reports nothing, and it fails in the
    direction that looks like diligence -- twenty-five lines of "delete these".

    It pointed at `ConsultedAudit.inert_entries` as "a real leave-one-out" in the same
    sentence. This is that, here.

    Reported rather than failed: an entry becomes inert when someone builds the
    constructor, which is good news and should not break a build.
    """
    global ALLOWED
    original = set(ALLOWED)
    base = set(analyse(declared, builders))
    inert = []
    for entry in sorted(original):
        ALLOWED = original - {entry}
        if not set(analyse(declared, builders)) - base:
            inert.append(entry)
    ALLOWED = original
    return inert


def self_test() -> int:
    """Seed each class this file claims to catch, and the near-misses it must not."""
    decl = "inductive Probe where\n  | quarry\n  | decoy\n"
    cases: list[tuple[str, dict[str, str], bool]] = [
        ("nothing builds it", {"a.lean": decl}, True),
        ("qualified construction",
         {"a.lean": decl, "b.lean": "def f : Probe := Probe.quarry\n"}, False),
        ("bare construction",
         {"a.lean": decl, "b.lean": "def f : Probe := .quarry\n"}, False),
        # A match arm is not a construction. This is the case that makes the tool
        # worth having: `AuthorityState.atomicShared` was matched on by
        # `PermitsOrdinaryWrite` and built by nothing.
        # Built on the *value* side of a match arm, which the pattern rule must not
        # mistake for the pattern side. A first version of that rule did, and
        # reported a constructor built inside an `if` in an arm body.
        ("built on the value side of an arm",
         {"a.lean": decl,
          "b.lean": "def f : Nat -> Probe\n  | 0 => .quarry\n  | _ => .decoy\n"}, False),
        ("matched but not built",
         {"a.lean": decl,
          "b.lean": "def f : Probe -> Nat\n  | .quarry => 0\n  | .decoy => 1\n"}, True),
        ("prose mentioning it",
         {"a.lean": decl, "b.lean": "/-- builds `Probe.quarry` one day -/\ndef f := 1\n"},
         True),
        ("string literal mentioning it",
         {"a.lean": decl, "b.lean": 'def f := "Probe.quarry"\n'}, True),
        # Flush-left constructors are a declaration the scanner must still see.
        # Review's four shapes, all silent before. A docstring may share the line, a
        # line may carry two constructors, an `inductive ... where` may carry them
        # itself, and a constructor may be capitalised.
        ("docstring on the constructor's own line",
         {"a.lean": "inductive Probe where" + chr(10)
                    + "  /-- doc -/ | quarry" + chr(10)}, True),
        ("two constructors on one line",
         {"a.lean": "inductive Probe where" + chr(10) + "  | quarry | decoy" + chr(10)}, True),
        ("inline inductive",
         {"a.lean": "inductive Probe where | quarry | decoy" + chr(10)}, True),
        ("flush-left constructors",
         {"a.lean": "inductive Probe where\n| quarry\n| decoy\n"}, True),
        # Documented blind spot, asserted: a constructor named in a theorem's own
        # statement reads as a construction, which is how `EventKind.fence` stayed
        # unreported while nothing could mint one.
        ("named only in a theorem about it",
         {"a.lean": decl,
          "b.lean": "theorem t (p : Probe) (h : p = Probe.quarry) : True := trivial\n"},
         False),
    ]
    failures = 0
    for label, sources, should_report in cases:
        reported = any("Probe.quarry" in line for line in analyse(sources))
        if reported != should_report:
            want = "reported" if should_report else "not reported"
            print(f"  SELF-TEST FAILED [{label}]: expected {want}")
            failures += 1

    # The builder corpus is a separate parameter, and no case above exercises it.
    builder_only = {"a.lean": decl}
    builders = {"a.lean": decl, "t.lean": "def f : Probe := .quarry\n"}
    if any("Probe.quarry" in line for line in analyse(builder_only, builders)):
        print("  SELF-TEST FAILED [builder corpus]: expected not reported")
        failures += 1

    # An allowlist entry must not exempt another inductive's constructor of the same
    # name. This was the first version's behaviour and it grew silently.
    global ALLOWED
    saved = ALLOWED
    ALLOWED = {"Decoy.quarry"}
    if not any("Probe.quarry" in line for line in analyse({"a.lean": decl})):
        print("  SELF-TEST FAILED [allowlist keying]: an entry for another inductive "
              "exempted this one")
        failures += 1
    ALLOWED = saved

    # Documented blind spot: namespace-blind, so another inductive's constructor of
    # the same name satisfies this one. Asserted so it cannot become silent coverage.
    other = decl + "\ninductive Decoy where\n  | quarry\n"
    if any("Probe.quarry" in line for line in
               analyse({"a.lean": other, "b.lean": "def f : Decoy := Decoy.quarry\n"})):
        print("  SELF-TEST FAILED [namespace blind spot]: this now discriminates; "
              "update the module docstring, which documents it as unhandled")
        failures += 1

    # The `--inert` sweep, both directions. It had neither, and reported every entry
    # in the allowlist as suppressing nothing for as long as it existed.
    ALLOWED = {"Probe.quarry"}
    if inert_entries({"a.lean": decl}, {"a.lean": decl}) != []:
        print("  SELF-TEST FAILED [inert sweep]: an entry that suppresses a real "
              "report is called inert")
        failures += 1
    ALLOWED = {"Probe.quarry", "Probe.decoy", "Nothing.here"}
    if inert_entries({"a.lean": decl}, {"a.lean": decl}) != ["Nothing.here"]:
        print("  SELF-TEST FAILED [inert sweep]: an entry that suppresses nothing is "
              "not reported, or a live one is")
        failures += 1
    ALLOWED = saved

    # `in_scope`, both directions, and the floor. `SCOPE` was a coverage claim with
    # nothing behind it: review dropped one token and this gate went silent for the
    # memory layer while still printing its success line. No self-test reached the
    # path filter, because every case here writes probes into a temporary directory
    # and calls the scanner directly.
    # **One case per `SCOPE` token.** This was `Memory` alone, and review measured
    # what that pinned: a leave-one-out over every token found 36 of 44 (gate,
    # token) pairs silent across the four scoped gates -- token deleted, self-test
    # green, gate green, success line printed. Seven were silent in all four,
    # `Obligation` among them, so dropping it took every `Grass/Obligation` file
    # out of every gate invisibly. That is the defect the plan records as closed,
    # reproduced against the subtree carrying `LedgerDelta.Applicable`.
    #
    # The floor cannot cover this and the docstring is right that it cannot: a
    # check derived from `SCOPE` is deleted along with the token. Only a
    # hard-coded name survives its removal, so there has to be one per token.
    if not in_scope(ROOT / "Grass" / "Certificate.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Certificate")
        failures += 1
    if not in_scope(ROOT / "Grass" / "Core" / "Context.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Core")
        failures += 1
    if not in_scope(ROOT / "Grass" / "Memory" / "State.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Memory")
        failures += 1
    if not in_scope(ROOT / "Grass" / "Obligation" / "Core.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Obligation")
        failures += 1
    if not in_scope(ROOT / "Grass" / "Op" / "Facets.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Op")
        failures += 1
    if not in_scope(ROOT / "Grass" / "Resource" / "Algebra.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Resource")
        failures += 1
    if not in_scope(ROOT / "Grass" / "Semantics" / "Execution.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Semantics")
        failures += 1
    if not in_scope(ROOT / "Grass" / "Std" / "Logical" / "Bag.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Std")
        failures += 1
    if not in_scope(ROOT / "Grass" / "Trust" / "Audit.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Trust")
        failures += 1
    if not in_scope(ROOT / "Grass" / "Verify" / "VerifiedProgram.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Verify")
        failures += 1
    if not in_scope(ROOT / "Tests" / "Foundation.lean"):
        print("  SELF-TEST FAILED: SCOPE lost Foundation")
        failures += 1
    if not in_scope(ROOT / "Tests" / "Memory" / "Loans.lean"):
        print("  SELF-TEST FAILED: Tests/Memory is out of scope")
        failures += 1
    if in_scope(ROOT / "Grass" / "ISA" / "X86" / "Decode.lean"):
        print("  SELF-TEST FAILED: Grass/ISA is in scope")
        failures += 1
    if in_scope(ROOT / "Grass" / "Process" / "Bag.lean"):
        print("  SELF-TEST FAILED: Grass/Process is in scope")
        failures += 1
    if scope_is_covered(DECLARED_IN, ("Grass",)):
        print("  SELF-TEST FAILED: a SCOPE subtree on disk reached no file")
        failures += 1

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
    if scannable(gapped).count(chr(10)) != gapped.count(chr(10)):
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
    if "MemoryState.alias" in scannable(crlf):
        print("  SELF-TEST FAILED: a CRLF string gap exposes the string's tail "
              "as source")
        failures += 1
    if scannable(crlf).count(chr(10)) != crlf.count(chr(10)):
        print("  SELF-TEST FAILED: a CRLF string gap loses a line")
        failures += 1

    # A **char literal** holding a quote must not open a string and blank the
    # rest of the line. Review put two door calls either side of one and watched
    # the second disappear.
    charlit = "def p := (alpha, " + chr(39) + chr(34) + chr(39) + ", omega)" + chr(10)
    if "omega" not in scannable(charlit):
        print("  SELF-TEST FAILED: a char literal holding a quote hides the "
              "rest of its line")
        failures += 1

    # Controls, so neither repair is a blanket disabling. A real string literal
    # is still blanked, and an apostrophe that is a *prime* on a name -- `h'`,
    # ordinary Lean -- does not start a literal and eat what follows.
    if "hidden" in scannable("def s := " + chr(34) + "hidden" + chr(34) + chr(10)):
        print("  SELF-TEST FAILED: a real string literal is no longer blanked")
        failures += 1
    if "visible" not in scannable("theorem h" + chr(39) + " : True := visible" + chr(10)):
        print("  SELF-TEST FAILED: a primed identifier swallows what follows it")
        failures += 1

    if failures:
        print(f"reachability audit self-test: {failures} failure(s)")
        return 1
    print("reachability audit self-test: all cases discriminate as documented")
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
    # The scope floor, before anything else runs. `SCOPE` is a coverage claim and
    # review showed it was one nothing checked: dropping a single token from it
    # switched this gate off for the memory layer and it printed its success line.
    uncovered_scope = scope_is_covered(DECLARED_IN, ("Grass",))
    if uncovered_scope:
        print(chr(10).join(uncovered_scope))
        print(chr(10) + "SCOPE names a subtree that reached no file. Widen the"
              " globs or correct SCOPE -- a gate that scans nothing passes.")
        return 1
    if "--self-test" in sys.argv:
        return self_test()
    if "--inert" in sys.argv:
        # Which entries suppress nothing. `ConsultedAudit.py` grew this after review
        # found eight of its twenty-one entries inert; this tool had the same defect
        # and no way to say so, and review then found twelve of thirty-seven here.
        # A listing rather than an exit code: an inert entry is not a violation of the
        # rule this tool enforces, it is a claim about the tree that has stopped being
        # true, and the fix is to delete it.
        global ALLOWED
        declared = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                    for path in DECLARED_IN}
        builders = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                    for path in BUILDERS_IN}
        inert = inert_entries(declared, builders)
        if inert:
            print("allowlist entries that suppress nothing: " + ", ".join(inert))
            print("Delete them, or say why the entry is kept with no effect.")
        else:
            print("reachability audit: every allowlist entry suppresses a report")
        return 0
    declared = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                for path in DECLARED_IN}
    builders = {path.relative_to(ROOT).as_posix(): path.read_text(encoding="utf-8")
                for path in BUILDERS_IN}
    if not declared:
        print(f"reachability audit: no sources found under {ROOT / 'Grass'}",
              file=sys.stderr)
        return 1
    unbuilt = analyse(declared, builders)
    if unbuilt:
        print("\n".join(sorted(unbuilt)))
        print("\nreachability audit: constructors nothing builds\n")
        print(
            f"{len(unbuilt)} unbuilt constructor(s). Build one, delete it, or add it "
            "to ALLOWED with the reason it is declared."
        )
        return 1
    print(
        "reachability audit: every declared constructor appears to be built "
        "(a lexical check; see the module docstring for what it does not cover)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
