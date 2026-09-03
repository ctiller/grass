#!/usr/bin/env python3
"""Report citations that name something which does not exist.

Prose in this project carries load. A docstring says "`foo_bar` is the proof", a
planning paragraph says "recorded in §4.2", and a reader who checks is expected to
find the thing. Three review rounds on the memory layer found citations that missed:

- `not_permitsOrdinaryWrite_of_not_exclusive`, named in two files as the borrow
  discipline, was renamed and neither reference followed;
- `ownerAuthority`, named in the plan, had become `authorityOf`;
- a debt "recorded in `docs/MEMORY_IMPLEMENTATION_PLAN.md` §4.2" was in §4.4.1, and
  §4.2 holds a different milestone's debts entirely.

None of these break a build. All of them are the same failure as a stale docstring:
prose asserting something a reader will not find, which is worse than silence
because it reads as a pointer.

**What this checks, exactly.**

1. **Declaration citations, in Lean comments only.** Every backticked token in a
   Lean comment that looks like a qualified or snake_case Lean identifier is looked
   up against the set of declaration names in the tree, matched on the final dotted
   component. If nothing declares it, it is reported.

   Most corpus documents are **not** scanned for these: they cite agent-bus event
   names (`review.merge_authorized`), JSON fields (`issue_kind`), and file names in
   the same backticks they cite theorems in, and no text scan separates those from
   Lean names.

   `LEAN_FACING_DOCS` is the exception, and it exists because the judgement above was
   wrong for one document. `MEMORY_IMPLEMENTATION_PLAN.md` cites declarations as
   *evidence* — "closed; `foo` is the theorem" — and review found eight dead ones in a
   single section, each presented as proof of a closed claim. A document that argues
   from Lean names is scanned like Lean.

2. **Section citations.** Every `§N` or `§N.M` that follows a document name in the
   same sentence is checked against that document's headings.

3. **Relative markdown links in Lean comments.** `check-doc-links.ps1` walks Markdown
   files, so a broken relative link inside a Lean docstring is outside every gate
   there is. There were three such links in the tree and one was wrong:
   `Grass/Memory/State.lean` is two directories deep and pointed at
   `../docs/FOUNDATION.md`, which is `Grass/docs/FOUNDATION.md`. Check 2 would have
   caught a bad *section* in that link and said nothing about the path. Only relative
   targets are resolved; an absolute URL is not this tool's business.

**What it does not check**, stated because an earlier tool in this directory
advertised a stronger reading and review corrected it:

- It matches short names, so `Foo.bar` and `Baz.bar` are indistinguishable. A
  citation naming the right leaf in the wrong namespace passes.
- A citation that is *stale but still resolves* — the name exists, but the theorem
  no longer says what the prose claims — is invisible here. It is invisible to
  `DocstringAudit.py` too, which only asks whether a claim-shaped sentence contains
  *some* backticked identifier. An earlier version of this line said the class was
  that tool's territory; review pointed out that it is nobody's, and that saying
  "covered over there" is worse than saying "covered nowhere".
- Backticked tokens with no `_` and no `.` are skipped, because ordinary prose is
  full of them (`Option`, `Nat`, `true`). So a bare renamed identifier like
  `compact` would not be caught.
- Section headings are matched by their leading number only. A pointer to a section
  that exists but says something else passes.

The allowlist below is where a citation that is deliberately not a declaration is
recorded, with the reason.

`--self-test` seeds each class this file claims to catch and asserts it is still
caught. Run it after changing the scanner: a silent audit is worse than none, and
the last tool added here was silent on its first version.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_FILES = sorted((ROOT / "Grass").rglob("*.lean")) + sorted((ROOT / "Tests").rglob("*.lean"))
DOC_FILES = sorted((ROOT / "docs").glob("*.md"))

# Documents that argue from Lean declaration names, and are scanned for them. See the
# module docstring: the plan cites theorems as evidence for closed claims, and eight
# of those citations were dead.
LEAN_FACING_DOCS = {"MEMORY_IMPLEMENTATION_PLAN.md", "MEMORY_VOCABULARY.md"}

# A declaration this tree introduces. `instance` is deliberately absent: anonymous
# instances have generated names nothing would cite.
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|def|abbrev|structure|inductive|class|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?]*)"
)
NAMESPACE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)")
CONSTRUCTOR = re.compile(r"^\s*\|\s*([a-z][A-Za-z0-9_']*)")
FIELD = re.compile(r"^\s{2,}(?:private\s+)?([a-z][A-Za-z0-9_']*)\s*:(?!=)")

# A backticked token worth checking. Requires an underscore or a dot, so ordinary
# prose words and single type names are skipped -- see the module docstring.
CITATION = re.compile(r"`([A-Za-z][A-Za-z0-9_.']*[_.][A-Za-z0-9_.']*)`")

# Root namespaces of Lean core and its standard library. A citation rooted here is
# not this tree's to declare. Enumerated rather than inferred: the alternative is
# elaborating against the toolchain, and this file is a text scan.
CORE_ROOTS = {
    "List", "Option", "Nat", "Int", "Bool", "BitVec", "Array", "String", "Char",
    "Prod", "Sigma", "Subtype", "Fin", "Decidable", "Function", "Classical", "Or",
    "And", "Iff", "Eq", "Ne", "Not", "Exists", "Sum", "UInt8", "UInt16", "UInt32",
    "UInt64", "USize", "Quot", "Sub", "Add", "Mul", "Lean", "IO", "Except", "Id",
}


def worth_checking(cited: str) -> bool:
    """Whether a backticked token is a citation this tool can adjudicate.

    Three exclusions, each of which was a false positive on the first run and each
    of which is a real limit rather than a tuning knob:

    - a file name (`Loan.lean`, `Spike1Reference.lean`) is not a declaration;
    - a token rooted in Lean core is not this tree's to declare;
    - an *expression* fragment -- `state.OutstandingObligations`, `fields.foldr`,
      `cpu.virtual` -- looks exactly like a qualified name. The rule is that a
      citation must either start upper-case or have an underscore in its final
      component, which keeps qualified declaration names and drops dot-notation on
      a lower-case binder. It also drops `cpu.virtual` and every other nominal
      string literal, which is right: those are `Name` values, not declarations.
    """
    if cited.endswith(".lean") or cited.endswith(".md") or cited.endswith(".py"):
        return False
    head, *_ = cited.split(".")
    if head in CORE_ROOTS:
        return False
    last = cited.split(".")[-1]
    return head[:1].isupper() or "_" in last

# `docs/NAME.md` §N.M, in either order and adjacent. Deliberately tight: a first
# version allowed 200 characters between them and matched a markdown table row
# where `RESOURCES.md` and an unrelated "RFC 9113 §5.2" sat in different cells.
# A loose pattern here reports the wrong document, which is worse than reporting
# nothing.
DOC_SECTION = re.compile(r"([A-Za-z_0-9]+\.md)`?\s*(?:section\s+|§+)(\d+(?:\.\d+)*)")
SECTION_DOC = re.compile(r"§+(\d+(?:\.\d+)*)\s+of\s+`?(?:docs/)?([A-Za-z_0-9]+\.md)")
HEADING = re.compile(r"^#{1,6}\s+(\d+(?:\.\d+)*)")

# Citations that are deliberately not declarations in this tree. Every entry says
# why; an unlisted unresolved citation fails the build, so the judgement is made
# once rather than rediscovered.
ALLOWED = {
    # Lean core and standard library names this project cites but does not declare.
    #
    # Eight names stood here that `--inert` reports as suppressing nothing, because
    # `worth_checking` already drops anything rooted in `CORE_ROOTS` -- `List`,
    # `Option`, `Nat`, `Decidable` -- so the tool never adjudicated them. An entry for
    # a citation the scanner is structurally blind to reads as a judgement somebody
    # made and is not one. `ByteStore.rec` is different and stays: `ByteStore` is this
    # tree's own type, so the root is not core and the generated recursor really is
    # unresolvable here.
    "ByteStore.rec",
    # Recursors and eliminators Lean generates for this tree's own types. Cited in
    # `Grass/Core/Uid.lean` and `Grass/Memory/ByteStore.lean` precisely because they
    # are generated rather than written, which is the point those comments make.
    "Uid.rec", "Uid.casesOn", "MemoryState.rec",
    # Module paths in import comments, which have the shape of a namespace.
    "Grass.Op.Facets",
    # Components another owner will build, named in the plan's ownership and
    # dependency sections. A plan that could not name what it depends on would be
    # useless, and these are not this layer's to declare.
    "Grass.ISA.X86", "Grass.Std.Owned", "Grass.ABI.Win64", "Grass.CFG",
    "Grass.Semantics", "Platform.Win32", "verify_assembly",
    # Names another owner declares, or has not yet: `Grass/Std` is the stdlib
    # agent's, and `Grass.Core.Id` is prose about a name deliberately not used.
    "Std.Owned", "Grass.Core.Id",
    # Lean *attribute* names, which have the shape of a declaration and are not
    # one. `Grass/Trust/Audit.lean` cites `implemented_by` because rejecting an
    # unverified `@[implemented_by]` replacement is what that module does; this
    # tool matches names lexically and cannot tell an attribute from a definition.
    "implemented_by",
    # --- Names in `Grass/Std/Logical` and `Tests/Std`, which arrived by merging main
    # --- and are another owner's. Split by reason, because two of these three
    # --- reasons are "not this tool's business" and one is a finding.
    #
    # Lean core and syntax, which this tool's declaration set does not include.
    "of_decide_eq_true", "beq_self_eq_true", "eq_of_beq", "macro_rules",
    # Modules another owner will build, named as dependencies.
    "Std.Process", "Std.Process.ByteFlow", "Grass.Effect", "ByteArray.toHost",
    # **Findings, not exemptions.** Each of these is cited as a local declaration and
    # nothing declares it: `built_two_ways` twice in `Tests/Std/VecVocabulary.lean`,
    # `Vec.concat` in `Grass/Std/Logical/Vec.lean`, `stable_merge_pass` and
    # `ByteStringOrder.lexicographicUnsigned` in `Grass/Std/Logical/Order.lean` and
    # `Tests/Std/StableSort.lean`, `write_all_loop` and `exit_no_progress` in
    # `Tests/Std/PartialWrite.lean`. They are exactly what this tool was written to
    # catch -- prose that reads as a pointer and points at nothing -- and they are
    # listed here rather than fixed because the modules belong to c-stdlib and the
    # names may be renames only that owner can resolve. Reported to them rather than
    # decided here; delete these entries when they answer.
    "built_two_ways", "Vec.concat", "stable_merge_pass",
    "ByteStringOrder.lexicographicUnsigned", "write_all_loop", "exit_no_progress",
    # Two path entries stood here -- `lean-toolchain` and `lakefile.toml` -- and
    # `worth_checking` drops a `.toml` suffix and a hyphenated token before the
    # allowlist is consulted, so neither did anything. Deleted for the same reason as
    # the core names above.
    # Prose about a name that was deleted, quoted so the reason survives. Each must
    # sit in a comment explaining why the thing no longer exists -- a reader finding
    # nothing is the point.
    #
    # **This is the weakest part of the tool and it has already been abused.**
    # `AuthorityGrant.Authorizes` was listed here on that ground, and two of its
    # three sites were describing the *present* enforcement chain, so the allowlist
    # was keeping a false claim green. Nothing checks that an entry's sites are all
    # historical, and nothing checks that an entry is still needed at all: review
    # found two with zero remaining sites. `--inert` checks the second half now, and
    # found two more -- `not_permitsOrdinaryWrite_of_not_exclusive`, whose only two
    # occurrences in the tree were this file's own docstring and its entry, and
    # `faultPointOutOfRange`, which has no `_` and no `.` so `worth_checking` rejects
    # it and the tool has never adjudicated the name at either of its live sites. An
    # entry for a citation the scanner is structurally blind to reads as "this dead
    # citation is deliberate" and is not even that. Both deleted. Before adding one,
    # read every site.
    "AccessIntent.isDevice",
    "AllocationRecord.initialized",
    "loan_refuses_only_the_frozen",
    # Deleted with `AuthorityProvider.loan` itself, when §3's rule moved into the
    # transition. Cited only as history, in a sentence that says it is gone.
    "loan_refuses_the_frozen",
    "MemoryState.grant",
}


def declared_names() -> set[str]:
    """Every short and qualified name this tree declares.

    Constructors and structure fields are included: prose cites
    `AuthorityState.frozen` and `AllocationRecord.live`, and neither is a
    `theorem`/`def` line.
    """
    names: set[str] = set()
    for path in LEAN_FILES:
        namespaces: list[str] = []
        text = path.read_text(encoding="utf-8")
        for line in text.splitlines():
            ns = NAMESPACE.match(line)
            if ns:
                namespaces.append(ns.group(1))
                # A namespace is a citable name: prose says "everything under
                # `Grass.Memory`". Every dotted suffix counts, because a module
                # opening `Grass.Std.Logical` cites it as `Std.Logical`.
                parts = ".".join(namespaces).split(".")
                for i in range(len(parts)):
                    names.add(".".join(parts[i:]))
                continue
            if line.startswith("end ") and namespaces:
                namespaces.pop()
                continue
            for pattern in (DECL, CONSTRUCTOR, FIELD):
                m = pattern.match(line)
                if m:
                    short = m.group(1)
                    names.add(short)
                    names.add(short.split(".")[-1])
                    if namespaces:
                        names.add(f"{namespaces[-1]}.{short}")
                    break
    return names


def sections_of(path: Path) -> set[str]:
    """The section numbers a document declares as headings."""
    out: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        m = HEADING.match(line)
        if m:
            out.add(m.group(1))
    return out


def comment_text(source: str) -> str:
    """Only the comments of a Lean source, with every other character blanked.

    **Blanked rather than concatenated, and it used to concatenate.** The old version
    returned the block comments followed by the line comments, and every caller then
    enumerated *that* string, so the number in every report about a `.lean` file was an
    index into a reconstruction. Review appended one bad citation at real line 433 of a
    431-line file and was sent to line 197 and line 231, two unrelated theorems -- and
    twice, because the line-comment regex matched the `--` inside the `/--` opener, so
    a docstring citation was scanned in both passes.

    `Tools/DoorAudit.py` had this defect and fixed it; the note there says "every line
    number from a real file was wrong". This is that fix, in the sibling that still had
    it. The line-comment pattern now refuses a `--` preceded by a slash.
    """
    out = [" " if character != chr(10) else chr(10) for character in source]
    for match in re.finditer(r"/-.*?-/", source, re.DOTALL):
        out[match.start():match.end()] = list(match.group(0))
    for match in re.finditer(r"(?<!/)--.*?$", source, re.MULTILINE):
        out[match.start():match.end()] = list(match.group(0))
    return "".join(out)


def check_declarations(prose: dict[str, str], names: set[str]) -> list[str]:
    """Report every backticked identifier-shaped citation nothing declares."""
    out: list[str] = []
    for where, text in prose.items():
        for number, line in enumerate(text.splitlines(), 1):
            for cited in CITATION.findall(line):
                if cited in ALLOWED or not worth_checking(cited):
                    continue
                if cited in names or cited.split(".")[-1] in names:
                    continue
                out.append(f"  {where}:{number}: `{cited}` is cited and nothing declares it")
    return out


def check_sections(prose: dict[str, str], sections: dict[str, set[str]]) -> list[str]:
    """Report every `docs/X.md ... §N` whose section X does not have."""
    out: list[str] = []
    for where, text in prose.items():
        for number, line in enumerate(text.splitlines(), 1):
            pairs = [(d, n) for d, n in DOC_SECTION.findall(line)]
            pairs += [(d, n) for n, d in SECTION_DOC.findall(line)]
            for doc, section in pairs:
                known = sections.get(doc)
                if known is None:
                    continue
                if section not in known:
                    out.append(
                        f"  {where}:{number}: cites {doc} §{section}, which it has no heading for"
                    )
    return out


RELATIVE_LINK = re.compile(r"\]\((\.{1,2}/[^)]+)\)")


def check_links(sources: dict[str, str]) -> list[str]:
    """Report every relative markdown link in a Lean comment that resolves to nothing.

    `check-doc-links.ps1` walks Markdown files, so a broken relative link inside a
    Lean docstring is outside every gate there is. There were three such links and
    one of them was wrong: `Grass/Memory/State.lean` is two directories deep and
    pointed at `../docs/FOUNDATION.md`, which is `Grass/docs/FOUNDATION.md`. The
    citation half of this tool would have caught a bad *section* in that link and
    said nothing about the path.
    """
    out: list[str] = []
    for where, text in sources.items():
        base = (ROOT / where).parent
        for number, line in enumerate(text.splitlines(), 1):
            for target in RELATIVE_LINK.findall(line):
                path = target.split("#", 1)[0]
                if not path:
                    continue
                if not (base / path).resolve().exists():
                    out.append(
                        f"  {where}:{number}: links to {target}, which does not exist "
                        f"relative to {Path(where).parent.as_posix()}"
                    )
    return out


def self_test() -> int:
    """Seed each class this file claims to catch.

    The cases are the three real misses that motivated it, plus the two documented
    blind spots asserted so they cannot quietly become coverage.
    """
    names = {"authorityOf", "MemoryState.authorityOf", "frozen", "AuthorityState.frozen"}
    sections = {"PLAN.md": {"4", "4.4", "4.4.1"}}
    failures = 0

    cases: list[tuple[str, dict[str, str], set[str], bool]] = [
        ("a renamed theorem",
         {"a.lean": "/-- see `not_a_real_name` -/"}, names, True),
        ("a name that exists",
         {"a.lean": "/-- see `MemoryState.authorityOf` -/"}, names, False),
        ("a short name that exists in some namespace",
         {"a.lean": "/-- see `AuthorityState.frozen` -/"}, names, False),
        # Code is not prose: a definition of the very name is not a citation of it,
        # and scanning code would make every file cite itself.
        ("code is not scanned",
         {"a.lean": "def not_a_real_name : Nat := 0\n"}, names, False),
    ]
    for label, sources, known, should_report in cases:
        prose = {k: comment_text(v) for k, v in sources.items()}
        reported = bool(check_declarations(prose, known))
        if reported != should_report:
            print(f"  SELF-TEST FAILED [{label}]: expected "
                  f"{'reported' if should_report else 'not reported'}")
            failures += 1

    section_cases = [
        ("a debt recorded in the wrong section",
         {"a.lean": "-- recorded in docs/PLAN.md §4.2\n"}, True),
        ("a section that exists",
         {"a.lean": "-- recorded in docs/PLAN.md §4.4.1\n"}, False),
        ("a document this tool does not know",
         {"a.lean": "-- see docs/OTHER.md §9.9\n"}, False),
    ]
    for label, sources, should_report in section_cases:
        prose = {k: comment_text(v) for k, v in sources.items()}
        reported = bool(check_sections(prose, sections))
        if reported != should_report:
            print(f"  SELF-TEST FAILED [{label}]: expected "
                  f"{'reported' if should_report else 'not reported'}")
            failures += 1

    # Documented blind spot: short-name matching cannot tell namespaces apart, so a
    # citation naming the right leaf in the wrong namespace passes. Asserted so it
    # cannot silently become coverage someone relies on.
    blind = {"a.lean": comment_text("/-- see `Wrong.frozen` -/")}
    if check_declarations(blind, names):
        print("  SELF-TEST FAILED [namespace blind spot]: this now reports; "
              "update the module docstring, which documents it as unhandled")
        failures += 1

    # Second blind spot: a bare token with no underscore or dot is not checked.
    bare = {"a.lean": comment_text("/-- see `gone` -/")}
    if check_declarations(bare, names):
        print("  SELF-TEST FAILED [bare-token blind spot]: this now reports; "
              "update the module docstring, which documents it as unhandled")
        failures += 1

    broken = {"Grass/Memory/State.lean": "-- see [F](../docs/FOUNDATION.md)"}
    if not check_links(broken):
        print("  SELF-TEST FAILED: a relative link that resolves to nothing is not "
              "reported")
        failures += 1

    good = {"Grass/Memory/State.lean": "-- see [F](../../docs/FOUNDATION.md)"}
    if check_links(good):
        print("  SELF-TEST FAILED: a relative link that resolves is reported")
        failures += 1

    anchored = {"Grass/Memory/State.lean":
                "-- see [F](../../docs/FOUNDATION.md#law-8)"}
    if check_links(anchored):
        print("  SELF-TEST FAILED: a link with a fragment is reported")
        failures += 1

    absolute = {"Grass/Memory/State.lean": "-- see [F](https://example.invalid/x.md)"}
    if check_links(absolute):
        print("  SELF-TEST FAILED: an absolute URL is reported; only relative links "
              "are resolvable here")
        failures += 1

    if failures:
        print(f"citation audit self-test: {failures} failure(s)")
        return 1
    print("citation audit self-test: all cases discriminate as documented")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()

    if "--inert" in sys.argv:
        # Which allowlist entries suppress nothing. `ConsultedAudit.py` grew this
        # first and `ReachabilityAudit.py` second, after each was found carrying
        # entries that had stopped doing anything; this file was the third, and its
        # ALLOWED comment says in so many words that "nothing checks that an entry
        # is still needed at all". Now something does.
        global ALLOWED
        names = declared_names()
        prose = {}
        for path in LEAN_FILES:
            prose[path.relative_to(ROOT).as_posix()] = comment_text(
                path.read_text(encoding="utf-8"))
        for path in DOC_FILES:
            prose[path.relative_to(ROOT).as_posix()] = path.read_text(encoding="utf-8")
        listed = sorted(ALLOWED)
        saved = ALLOWED
        ALLOWED = set()
        reported = " ".join(check_declarations(prose, names))
        ALLOWED = saved
        inert = [entry for entry in listed if entry not in reported]
        if inert:
            print("allowlist entries that suppress nothing: " + ", ".join(inert))
            print("Delete them, or say why the entry is kept with no effect.")
        else:
            print("citation audit: every allowlist entry suppresses a report")
        return 0

    names = declared_names()
    sections = {path.name: sections_of(path) for path in DOC_FILES}

    prose: dict[str, str] = {}
    for path in LEAN_FILES:
        prose[path.relative_to(ROOT).as_posix()] = comment_text(
            path.read_text(encoding="utf-8"))
    # Section citations are matched within a comment *block* rather than within a
    # line, because a docstring wraps and "`docs/INSTRUCTIONS.md`\n§4" was invisible
    # to a per-line scan -- twenty-eight such pairs, against the two hundred and
    # forty it saw. Joining the whole file would reintroduce the false positive the
    # tight pattern exists to avoid, where a document name and an unrelated "RFC
    # 9113 §5.2" sit in different cells of one markdown table row, so the join is
    # per block.
    #
    # **Blanked in place rather than concatenated**, for the reason `comment_text`
    # above gives: a concatenation makes every reported line number an index into a
    # reconstruction. That fix landed for the declaration half and not for this one,
    # one round after the note saying it had -- a section citation at real line 433 of
    # a 431-line file was reported at line 36. Each block is flattened onto its own
    # first line and the rest of the file is blank, so the join is still per block
    # and the number reported is the source's.
    joined: dict[str, str] = {}
    for path in LEAN_FILES:
        source = path.read_text(encoding="utf-8")
        out = [""] * len(source.splitlines())
        for match in re.finditer(r"/-.*?-/", source, re.DOTALL):
            first = source[: match.start()].count(chr(10))
            out[first] = " ".join(
                line.strip() for line in match.group(0).splitlines())
        joined[path.relative_to(ROOT).as_posix()] = chr(10).join(out)
    documents: dict[str, str] = {}
    for path in DOC_FILES:
        documents[path.relative_to(ROOT).as_posix()] = path.read_text(encoding="utf-8")

    lean_facing = {name: text for name, text in documents.items()
                   if Path(name).name in LEAN_FACING_DOCS}
    problems = (check_declarations(prose, names)
                + check_declarations(lean_facing, names)
                + check_sections(joined, sections)
                # Line comments too. `comment_text` keeps them and keeps the line
                # structure, and `DOC_SECTION` requires the document name and the
                # section mark on one line, so a line comment needs no joining. The
                # section half scanned block comments only, while the module docstring
                # claimed it checked every section mark following a document name in
                # the same sentence; review put a wrong section in a line comment and
                # the audit passed.
                + check_sections(prose, sections)
                + check_sections(documents, sections)
                + check_links(prose))
    if problems:
        print("\n".join(sorted(problems)))
        print("\ncitation audit: prose naming something that does not exist\n")
        print(
            f"{len(problems)} bad citation(s). Fix the name or the section, or add "
            "the citation to ALLOWED with the reason it resolves to nothing."
        )
        return 1
    print(
        "citation audit: every cited declaration, document section and relative link "
        "resolves "
        "(a lexical check; see the module docstring for what it does not cover)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
