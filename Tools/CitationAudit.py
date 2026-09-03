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

   Corpus documents are **not** scanned for these. They cite agent-bus event names
   (`review.merge_authorized`), JSON fields (`issue_kind`), and file names in the
   same backticks they cite theorems in, and no text scan separates those from Lean
   names. Documents are scanned for section citations only, which is where the real
   miss was anyway.

2. **Section citations.** Every `§N` or `§N.M` that follows a document name in the
   same sentence is checked against that document's headings.

**What it does not check**, stated because an earlier tool in this directory
advertised a stronger reading and review corrected it:

- It matches short names, so `Foo.bar` and `Baz.bar` are indistinguishable. A
  citation naming the right leaf in the wrong namespace passes.
- A citation that is *stale but still resolves* — the name exists, but the theorem
  no longer says what the prose claims — is invisible here. That is
  `DocstringAudit.py`'s territory and it is not closed by either tool.
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
    "List.findSome?", "List.getElem?", "List.eq_nil_of_length_eq_zero",
    "List.getElem?_take", "List.getElem?_drop", "Option.any", "Nat.pow_le_pow_right",
    "ByteStore.rec", "Decidable.decide",
    # Recursors and eliminators Lean generates for this tree's own types. Cited in
    # `Grass/Core/Uid.lean` and `Grass/Memory/ByteStore.lean` precisely because they
    # are generated rather than written, which is the point those comments make.
    "Uid.rec", "Uid.casesOn",
    # Module paths in import comments, which have the shape of a namespace.
    "Grass.Op.Facets",
    # Names another owner declares, or has not yet: `Grass/Std` is the stdlib
    # agent's, and `Grass.Core.Id` is prose about a name deliberately not used.
    "Std.Owned", "Grass.Core.Id",
    # Paths and file names, which happen to match the identifier shape.
    "lean-toolchain", "lakefile.toml",
    # Prose about a name that was deleted, quoted so the reason survives. Each is
    # named in a comment explaining why the thing no longer exists, so a reader
    # finding nothing is the point.
    "AccessIntent.isDevice",
    "AllocationRecord.initialized",
    "not_permitsOrdinaryWrite_of_not_exclusive",
    "loan_refuses_only_the_frozen",
    "AuthorityGrant.Authorizes",
    "MemoryState.grant",
    "faultPointOutOfRange",
    "atomicsAreNever_",
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
    """Only the comments of a Lean source, so code is not scanned as prose."""
    blocks = re.findall(r"/-.*?-/", source, re.DOTALL)
    lines = re.findall(r"--.*?$", source, re.MULTILINE)
    return "\n".join(blocks + lines)


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

    if failures:
        print(f"citation audit self-test: {failures} failure(s)")
        return 1
    print("citation audit self-test: all cases discriminate as documented")
    return 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()

    names = declared_names()
    sections = {path.name: sections_of(path) for path in DOC_FILES}

    prose: dict[str, str] = {}
    for path in LEAN_FILES:
        prose[path.relative_to(ROOT).as_posix()] = comment_text(
            path.read_text(encoding="utf-8"))
    documents: dict[str, str] = {}
    for path in DOC_FILES:
        documents[path.relative_to(ROOT).as_posix()] = path.read_text(encoding="utf-8")

    problems = (check_declarations(prose, names)
                + check_sections(prose, sections)
                + check_sections(documents, sections))
    if problems:
        print("\n".join(sorted(problems)))
        print("\ncitation audit: prose naming something that does not exist\n")
        print(
            f"{len(problems)} bad citation(s). Fix the name or the section, or add "
            "the citation to ALLOWED with the reason it resolves to nothing."
        )
        return 1
    print(
        "citation audit: every cited declaration and document section exists "
        "(a lexical check; see the module docstring for what it does not cover)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
