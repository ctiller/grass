//! Check that every `Vec`-returning operation states what its result observes.
//!
//! `docs/STDLIB.md` observation coverage requires that every operation
//! returning a `Vec` state a law computing the result's `length` **and** a law
//! computing the result's `get?`, in terms of its arguments'. This tool checks it.
//!
//! # Why it is a program and not a paragraph
//!
//! The rule has been rewritten three times. Every version was stated in prose, and
//! every version was violated in the same commit that stated it -- the "at least one
//! law" rule shipped alongside `truncate` and `clear`, which had none; the
//! "determination" rule shipped alongside an internal inconsistency about
//! `splitAt`; and the coverage rule itself shipped alongside `Vec.sum` and
//! `Vec.count`, which had no laws at all, with `sum` on the right-hand side of
//! `Vec.length_flatten` where every consumer of that law would meet it.
//!
//! That is not carelessness three times. It is what an unenforced rule does to a
//! library changing at this rate, and it was adversarial review rather than the
//! author that caught each one.
//!
//! # What it checks, and what it deliberately does not
//!
//! A declaration is an **operation** if it is a `def` in `Grass.Std.Logical.Vec`
//! whose result type is a `Vec`. For each, the audit looks for a theorem somewhere
//! in the environment whose statement applies `Vec.length` to a term headed by that
//! operation, and likewise for `Vec.get?`.
//!
//! It has been attacked, and it failed once. The first version accepted an operation
//! carrying `(f v i).length = (f v i).length` and `(f v i).get? j = (f v i).get? j`
//! -- two `rfl` self-laws -- and counted it as covered. That is the same attack
//! adversarial review had used to break the *prose* rule, and it worked on the
//! checker too. [`Skeleton::observes_non_vacuously`] is the fix: an equation counts
//! only if the side that does not observe the operation also does not mention it.
//!
//! Four deliberate limits, stated because a checker that overstates its reach is
//! worse than none:
//!
//! - A law stated over the `v[i]?` notation rather than `Vec.get?` would not be
//!   seen, since `GetElem?.getElem?` is a different constant. No law in the library
//!   is currently written that way, but the audit would produce a false failure if
//!   one were.
//! - It does not check that a law is *correct*, only that it exists and is about the
//!   right thing. The kernel checks correctness.
//! - It does not reach operations returning `Bool`, `Nat`, `Option`, or `Prop` --
//!   roughly half the module. Decision 6's clause (i) is phrased over `length` and
//!   `get?` of a result, which presupposes the result is a `Vec`. Those operations
//!   are counted and listed as outside the bar rather than silently passed, so the
//!   number is visible.
//! - It does not implement clause (ii), the `empty`/`push` recursion, nor the alias
//!   clause. Operations that pass on those are named in [`RECURSION_OR_ALIAS`] and
//!   the exemption is explicit, which is the point: an exemption in a list is
//!   reviewable, an exemption in prose is not.
//!
//! # Where the facts come from, and where the policy lives
//!
//! This was a Lean meta-program, and half of it still has to be: whether a constant
//! is a `def`, what its type is, and what every theorem in the environment states
//! are questions only an elaborated environment can answer. What does *not* need
//! Lean is the judging -- the namespace test, the internal-name test, the
//! result-type test, the three `Expr` predicates, the exemption list and the
//! report. That half moved here, where it is unit-testable without a six-minute
//! Lean build behind every assertion.
//!
//! So [`facts_lean_source`] generates a meta-program that dumps *facts* and makes no
//! decisions, `lake env lean` elaborates it under the repository's pinned toolchain,
//! and [`audit`] is the whole of the policy. Nothing about the rule is written in
//! Lean any more, which is what retires the checked-in file this replaces.
//!
//! ## Why the fact dump is not filtered, and where it still is
//!
//! A sibling port was returned by review for exactly the defect this section exists
//! to avoid. Its generated meta-program selected which declarations to report and
//! the Rust half only rejected records it considered stray, so an *over*-inclusive
//! Lean predicate was caught and an *under*-inclusive one was invisible: a predicate
//! that skipped a shape -- or skipped everything -- produced fewer records, the
//! counts stayed self-consistent, and the audit reported clean over a set that was
//! missing the very declarations it was supposed to judge. A fail-open trust gate.
//!
//! Two things close that here.
//!
//! First, the record set opens with an **unfiltered census**: one `K` record for
//! every constant in `env.constants`, in enumeration order, carrying its kind, its
//! `Name.isInternal` flag and its name. No predicate stands between the environment
//! and that list. Every set this tool works over is then derived *here* from the
//! census -- [`name_is_prefix_of`] draws the namespace, [`name_is_internal`] drops
//! the internals, [`Skeleton::returns_vec`] draws the bar.
//!
//! Second, the type skeletons (`S` records) *are* emitted under a Lean-side
//! condition, because dumping the type of all two hundred thousand constants would
//! cost more than the audit. That condition is `vecNs.isPrefixOf name || isThm`, and
//! [`audit`] recomputes the required index set from the census and demands **exact
//! agreement**: a skeleton for an index the policy did not ask for is an error, and
//! -- the direction the sibling missed -- a missing skeleton for an index the policy
//! did ask for is an error naming the declaration. A narrowed Lean predicate is
//! therefore a loud mismatch and not a smaller, self-consistent report.
//!
//! The same shape covers `Name.isInternal`: the census carries Lean's answer for
//! every constant, [`name_is_internal`] computes this tool's answer from the printed
//! name, and a single disagreement anywhere in the environment is a refusal. That
//! comparison runs over every constant on every invocation, so the reimplementation
//! is checked against the original rather than trusted.
//!
//! What remains trusted of the Lean half is that `env.constants` enumerates the
//! environment, and that a kind tag and a type skeleton describe the constant they
//! are attached to. Those are total functions of each constant, not selections, so
//! they can be wrong but they cannot silently shrink the set being judged. The
//! `Z` terminator carries both record counts, so a Lean process killed part-way
//! through is a refusal rather than a shorter environment.
//!
//! # Two deliberate departures from the Lean original
//!
//! **An empty environment was a clean audit.** The original counted operations,
//! found none, and printed "0 Vec-returning operations each carry a length law and a
//! get? law" with status 0. Run against a tree where `Grass/Std/Logical/Vec.lean` had
//! been renamed, emptied or sparse-checked out, it reported success over nothing --
//! which is how a gate stops gating without anyone noticing, and is a measured
//! failure mode of another tool in this repository. This port refuses: the source
//! files it depends on are checked before Lean is invoked and named in the failure,
//! the two observation constants must be in the census, and finding no operations at
//! all is an error rather than a clean report. See [`Audit::refuse_missing_rule`]
//! and [`Audit::refuse_no_operations`].
//!
//! **A dead exemption stayed exempt.** [`RECURSION_OR_ALIAS`] excuses nine
//! declarations by name. The original never checked that those names existed, so
//! renaming an exempt operation silently moved it out of the exemption *and* the
//! summary line kept counting nine, because the count was the list's length rather
//! than the number of declarations it excused. An exemption list that cannot rot is
//! the whole argument for having one, so this port refuses a list naming a
//! declaration the environment does not have.
//!
//! Everything else is the original's behaviour, including the two summary and
//! failure texts, which are reproduced verbatim so a differential against the Lean
//! tool compares strings rather than paraphrases. The one unavoidable difference is
//! framing: `throwError` decorated the failure with a source position and the word
//! `error`, and this port writes the same message to standard error and exits 1.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::process::{Command, ExitCode};

// ---------------------------------------------------------------------------
// The rule.
// ---------------------------------------------------------------------------

/// The namespace the bar is drawn around.
const VEC_NS: &str = "Grass.Std.Logical.Vec";

/// The observations decision 6 is phrased over.
const LENGTH_NAME: &str = "Grass.Std.Logical.Vec.length";

/// The checked accessor.
const GET_NAME: &str = "Grass.Std.Logical.Vec.get?";

/// A law is an equation, and this is the constant an equation is headed by.
///
/// The bare `Eq`, because that is what `` `Eq `` elaborates to and what appears at
/// the head of every `a = b` in a theorem statement.
const EQ_NAME: &str = "Eq";

/// The modules the audit elaborates, and therefore the environment it judges.
///
/// This is the Lean original's import list unchanged, and it is a policy choice
/// rather than a detail: a law stated in a module outside this list is not seen, so
/// widening the list can only turn findings into passes. That is the fail-open
/// direction, so it is not widened without deciding to.
const AUDIT_IMPORTS: &[&str] = &["Grass.Std.Logical.Vec", "Grass.Std.Logical.Order"];

/// The files on disk those imports are compiled from.
///
/// Checked before Lean is invoked, so running from the wrong directory is a
/// diagnosis in a millisecond rather than an opaque elaboration failure a minute
/// later -- and never a clean report over an empty environment.
const AUDIT_SOURCES: &[&str] = &["Grass/Std/Logical/Vec.lean", "Grass/Std/Logical/Order.lean"];

/// Operations that satisfy decision 6 by its clause (ii) or its alias clause rather
/// than by a `length`/`get?` pair, with the reason.
///
/// Listed rather than inferred, so that adding one is a reviewable edit. Adversarial
/// review found that the alias clause as originally worded admitted a cycle -- two
/// operations each citing the other and neither carrying a law -- so an alias
/// exemption is only as good as the fact that a human wrote it down here.
///
/// The `append` entry is the first thing this audit found, and it is worth recording
/// what kind of finding it is. `Vec.length_append` and the two `get?_append_*` laws
/// exist, but every one is stated over `v ++ w`, which elaborates through the
/// `Append` instance rather than as an application of `Vec.append`. So the laws
/// cover the operation *as consumers write it* and leave the bare name uncovered.
///
/// That is a naming observation rather than a missing law, which is why it is an
/// exemption with a reason instead of a weakening of the check. The alternative --
/// teaching the audit to see through instance applications -- would make it accept a
/// class of genuine gaps in exchange for tidying one false one.
///
/// Every name here must be a constant the environment has; see
/// [`Audit::refuse_dead_exemptions`].
const RECURSION_OR_ALIAS: &[(&str, &str)] = &[
    (
        "Grass.Std.Logical.Vec.foldl",
        "clause (ii): foldl_empty, foldl_push",
    ),
    (
        "Grass.Std.Logical.Vec.foldr",
        "clause (ii): foldr_empty, foldr_push",
    ),
    (
        "Grass.Std.Logical.Vec.flatten",
        "clause (ii): flatten_empty, flatten_push",
    ),
    (
        "Grass.Std.Logical.Vec.pop?",
        "clause (ii): pop?_empty, pop?_push",
    ),
    (
        "Grass.Std.Logical.Vec.truncate",
        "alias: truncate_eq_take, and take passes (i)",
    ),
    (
        "Grass.Std.Logical.Vec.clear",
        "alias: clear_eq_empty, and empty passes (i)",
    ),
    (
        "Grass.Std.Logical.Vec.splitAt",
        "alias: splitAt_eq, and take/drop pass (i)",
    ),
    (
        "Grass.Std.Logical.Vec.fromList",
        "the constructor; toList_fromList characterises it",
    ),
    (
        "Grass.Std.Logical.Vec.append",
        "laws stated over the `++` notation: length_append, get?_append_left, get?_append_right",
    ),
];

// ---------------------------------------------------------------------------
// Lean names, reimplemented over their printed form.
// ---------------------------------------------------------------------------

/// Split a printed `Lean.Name` into its components.
///
/// `Name.toString` joins components with `.` and wraps a component that is not a
/// legal identifier in `«»`, so a dot inside guillemets belongs to a component and
/// is not a separator. A numeric component prints as bare digits.
fn name_components(name: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (offset, ch) in name.char_indices() {
        match ch {
            '\u{ab}' => depth += 1,
            '\u{bb}' => depth = depth.saturating_sub(1),
            '.' if depth == 0 => {
                parts.push(&name[start..offset]);
                start = offset + 1;
            }
            _ => {}
        }
    }
    parts.push(&name[start..]);
    parts
}

/// `Lean.Name.isPrefixOf`, which counts a name as a prefix of itself.
///
/// Compared component by component rather than as a flat string, so
/// `Grass.Std.Logical.Vector` is not under `Grass.Std.Logical.Vec` and a component
/// that had to be escaped -- `Grass.Std.Logical.«Vec.probe»` -- is one component and
/// not two.
fn name_is_prefix_of(prefix: &str, name: &str) -> bool {
    let prefix = name_components(prefix);
    let name = name_components(name);
    prefix.len() <= name.len() && prefix.iter().zip(name.iter()).all(|(a, b)| a == b)
}

/// `Lean.Name.isInternal`: any string component whose first character is `_`.
///
/// Lean's definition is over the structured name -- `str p s => s.front == '_' ||
/// isInternal p`, with a numeric component contributing nothing of its own -- and
/// this reads the same property off the printed form. A component that had to be
/// escaped is tested on its contents rather than on the opening guillemet.
///
/// It is not trusted. The census carries Lean's answer for every constant in the
/// environment and [`Audit::refuse_internal_disagreement`] refuses if this function
/// disagrees anywhere, so the reimplementation is checked against the original on
/// every run rather than argued for in this comment.
fn name_is_internal(name: &str) -> bool {
    name_components(name).into_iter().any(|part| {
        let part = part
            .strip_prefix('\u{ab}')
            .map(|rest| rest.strip_suffix('\u{bb}').unwrap_or(rest))
            .unwrap_or(part);
        part.starts_with('_')
    })
}

// ---------------------------------------------------------------------------
// The record format.
// ---------------------------------------------------------------------------

/// What a constant is, as far as this audit cares.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    /// `ConstantInfo.defnInfo`: a candidate operation.
    Def,
    /// `ConstantInfo.thmInfo`: a candidate law.
    Thm,
    /// Anything else: axioms, constructors, inductives, recursors, `opaque`, `quot`.
    Other,
}

/// One line of the unfiltered census.
#[derive(Clone, Debug)]
struct Entry {
    kind: Kind,
    /// `Lean.Name.isInternal` as the elaborator computed it, kept only so
    /// [`name_is_internal`] can be checked against it.
    lean_internal: bool,
    name: String,
}

/// Undo [`facts_lean_source`]'s field escaping.
///
/// The record format reserves space, tab, newline, carriage return and backslash;
/// every one of them is legal inside a `Lean.Name` component, which is why they are
/// escaped rather than assumed absent.
fn unescape(field: &str) -> Result<String, String> {
    if !field.contains('\\') {
        return Ok(field.to_string());
    }
    let mut out = String::with_capacity(field.len());
    let mut chars = field.chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        match chars.next() {
            Some('\\') => out.push('\\'),
            Some('t') => out.push('\t'),
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('s') => out.push(' '),
            Some(other) => return Err(format!("unknown escape \\{other}")),
            None => return Err("a field ends in a backslash".to_string()),
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Expression skeletons.
// ---------------------------------------------------------------------------

/// The `Lean.Expr` constructors the four predicates below distinguish.
///
/// Everything the predicates never look inside -- `bvar`, `fvar`, `mvar`, `sort`,
/// `lit` -- is [`Tag::Atom`], because the Lean original's recursion returns `false`
/// on all of them and a binder's name and info are read by none of it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tag {
    App,
    Lam,
    Forall,
    Let,
    MData,
    Proj,
    Const,
    Atom,
}

impl Tag {
    /// How many subterms the Lean original's recursion descends into.
    fn arity(self) -> usize {
        match self {
            Tag::App | Tag::Lam | Tag::Forall => 2,
            Tag::Let => 3,
            Tag::MData | Tag::Proj => 1,
            Tag::Const | Tag::Atom => 0,
        }
    }
}

/// A name this audit compares against; anything else is [`NO_NAME`].
///
/// Equality is only ever tested against the handful of constants the rule names --
/// `Vec`, `Vec.length`, `Vec.get?`, `Eq` and the operations -- so the parser resolves
/// a constant to an id from that table and forgets every other name. Interning the
/// nineteen million constant occurrences in the environment would cost more than the
/// audit and buy nothing.
type NameId = u32;

/// Not one of the names this audit compares against.
const NO_NAME: NameId = NameId::MAX;

/// The names an expression is parsed against.
#[derive(Default)]
struct NameTable {
    ids: HashMap<String, NameId>,
}

impl NameTable {
    fn intern(&mut self, name: &str) -> NameId {
        if let Some(id) = self.ids.get(name) {
            return *id;
        }
        let id = self.ids.len() as NameId;
        assert!(id != NO_NAME, "the interesting-name table is small");
        self.ids.insert(name.to_string(), id);
        id
    }

    fn lookup(&self, name: &str) -> NameId {
        self.ids.get(name).copied().unwrap_or(NO_NAME)
    }
}

/// A `Lean.Expr` reduced to what the rule reads: shape, and the names at heads.
///
/// Nodes are in preorder, so a subterm occupies a contiguous range and `end[i]` is
/// enough to navigate: node `i`'s first subterm is at `i + 1`, its second at
/// `end[i + 1]`, its third at `end[end[i + 1]]`.
#[derive(Debug)]
struct Skeleton {
    tag: Vec<Tag>,
    /// The interned name of a [`Tag::Const`] node; [`NO_NAME`] for every other node.
    name: Vec<NameId>,
    /// One past the last node of the subterm rooted at this node.
    end: Vec<u32>,
    /// The node `Lean.Expr.getAppFn` returns for this node.
    ///
    /// `getAppFn` walks down the `app` spine and, notably, does *not* step through
    /// `mdata`; this reproduces that.
    head: Vec<u32>,
}

impl Skeleton {
    /// Parse the token stream [`facts_lean_source`] writes.
    ///
    /// Tokens are the constructor letters in preorder, with a constant written as
    /// `c` followed by its escaped name. A stream that does not describe exactly one
    /// well-formed term is refused: `end[0] == nodes` is that condition, since a
    /// truncated term leaves a child index past the end and a trailing token leaves
    /// the root's subterm short of it.
    fn parse(tokens: &str, names: &NameTable) -> Result<Skeleton, String> {
        let mut tag = Vec::new();
        let mut name = Vec::new();
        for token in tokens.split(' ') {
            let (t, n) = match token {
                "a" => (Tag::App, NO_NAME),
                "l" => (Tag::Lam, NO_NAME),
                "f" => (Tag::Forall, NO_NAME),
                "e" => (Tag::Let, NO_NAME),
                "m" => (Tag::MData, NO_NAME),
                "p" => (Tag::Proj, NO_NAME),
                "x" => (Tag::Atom, NO_NAME),
                _ => match token.strip_prefix('c') {
                    Some(rest) => (Tag::Const, names.lookup(&unescape(rest)?)),
                    None => return Err(format!("{token:?} is not a term token")),
                },
            };
            tag.push(t);
            name.push(n);
        }
        let nodes = tag.len();
        if nodes == 0 {
            return Err("a term with no tokens".to_string());
        }

        let mut end = vec![0u32; nodes];
        for index in (0..nodes).rev() {
            let mut child = index + 1;
            for _ in 0..tag[index].arity() {
                if child >= nodes {
                    return Err(format!(
                        "the term ends part-way through the subterms of token {index}"
                    ));
                }
                child = end[child] as usize;
            }
            end[index] = child as u32;
        }
        if end[0] as usize != nodes {
            return Err(format!(
                "the term describes {} of its {nodes} tokens, so it is not one term",
                end[0]
            ));
        }

        let mut head = vec![0u32; nodes];
        for index in (0..nodes).rev() {
            head[index] = if tag[index] == Tag::App {
                head[index + 1]
            } else {
                index as u32
            };
        }
        Ok(Skeleton {
            tag,
            name,
            end,
            head,
        })
    }

    /// The name `Lean.Expr.getAppFn e |>.constName?` returns, or [`NO_NAME`].
    fn head_name(&self, node: usize) -> NameId {
        self.name[self.head[node] as usize]
    }

    /// The second subterm of a two- or three-place node.
    fn child1(&self, node: usize) -> usize {
        self.end[node + 1] as usize
    }

    /// `Lean.Expr.getAppArgs`, in application order.
    fn app_args(&self, node: usize) -> Vec<usize> {
        let mut args = Vec::new();
        let mut spine = node;
        while self.tag[spine] == Tag::App {
            args.push(self.child1(spine));
            spine += 1;
        }
        args.reverse();
        args
    }

    /// Whether the subterm at `root` contains `op` anywhere.
    ///
    /// The original is `e.getAppFn.constName? == some op` at every node of the
    /// recursion; because a subterm is a contiguous range this is that same test
    /// over that range.
    fn mentions(&self, op: NameId, root: usize) -> bool {
        (root..self.end[root] as usize).any(|node| self.head_name(node) == op)
    }

    /// Whether the subterm at `root` applies `obs` to a term headed by `op`.
    fn observes(&self, obs: NameId, op: NameId, root: usize) -> bool {
        (root..self.end[root] as usize).any(|node| {
            self.head_name(node) == obs
                && self
                    .app_args(node)
                    .into_iter()
                    .any(|arg| self.head_name(arg) == op)
        })
    }

    /// Whether the subterm at `root` contains an equation observing `op` on one side
    /// whose *other* side does not mention `op`.
    ///
    /// This is the non-vacuity condition, and it exists because the audit without it
    /// was fooled by exactly the attack adversarial review used against the prose
    /// rule. A probe operation carrying
    ///
    /// ```text
    /// @[simp] theorem length_probe (v) (i) : (probe v i).length = (probe v i).length := rfl
    /// ```
    ///
    /// compiles, is wrong, and satisfied "a law computing its length" -- the audit
    /// counted it and reported success. Requiring the other side to be free of `op`
    /// is what makes a law say something about the operation rather than about
    /// itself, and it is the mechanical form of decision 6's "neither may be `f`'s
    /// own definitional body".
    fn observes_non_vacuously(&self, eq: NameId, obs: NameId, op: NameId, root: usize) -> bool {
        (root..self.end[root] as usize).any(|node| {
            if self.head_name(node) != eq {
                return false;
            }
            let args = self.app_args(node);
            // `Eq` applied to anything but its type and two sides is not an equation
            // this rule can read, exactly as the original's three-element match.
            if args.len() != 3 {
                return false;
            }
            let (lhs, rhs) = (args[1], args[2]);
            (self.observes(obs, op, lhs) && !self.mentions(op, rhs))
                || (self.observes(obs, op, rhs) && !self.mentions(op, lhs))
        })
    }

    /// Whether a constant's result type is a `Vec`.
    ///
    /// Walks past the binders and asks what the head of what is left is. Like the
    /// original it does not step through `mdata`, and like the original it does not
    /// reduce: a definition whose result type is a `def` that unfolds to `Vec` is
    /// outside the bar.
    fn returns_vec(&self, vec: NameId) -> bool {
        let mut node = 0usize;
        while self.tag[node] == Tag::Forall {
            node = self.child1(node);
        }
        self.head_name(node) == vec
    }
}

// ---------------------------------------------------------------------------
// The audit.
// ---------------------------------------------------------------------------

/// What the audit found, before it is written out.
#[derive(Debug)]
struct Outcome {
    /// Every definition inside the bar: the Lean original's `ops`.
    operations: Vec<String>,
    /// Those of them the exemption list does not excuse: the original's `checked`.
    checked: Vec<String>,
    /// Vec-namespace definitions the bar does not reach.
    outside_bar: Vec<String>,
    /// `(operation, why it fails)`, in census order.
    missing: Vec<(String, String)>,
}

impl Outcome {
    /// The Lean original's `logInfo`, reproduced so a differential compares strings.
    fn success_line(&self) -> String {
        format!(
            "observation-coverage audit: {} Vec-returning operations each carry a length law and \
             a get? law; {} exempt by clause (ii) or the alias clause; {} declarations outside \
             the bar's reach",
            self.checked.len(),
            RECURSION_OR_ALIAS.len(),
            self.outside_bar.len()
        )
    }

    /// The Lean original's `throwError`, reproduced likewise.
    fn failure_message(&self) -> String {
        let mut message = String::from(
            "observation-coverage audit failed; docs/STDLIB.md observation coverage \
             requires a length law and a get? law for every Vec-returning operation:",
        );
        for (name, why) in &self.missing {
            let _ = write!(message, "\n  {name}: {why}");
        }
        message
    }
}

/// The census, and the derived sets the policy draws from it.
#[derive(Debug)]
struct Audit {
    census: Vec<Entry>,
    /// Index of every constant under the `Vec` namespace, in census order.
    vec_namespace: Vec<usize>,
    /// Index of every theorem, in census order.
    theorems: Vec<usize>,
    /// Index of every constant the record set carries a type skeleton for.
    skeletons: HashSet<usize>,
}

impl Audit {
    /// The census disagreeing with [`name_is_internal`] means this tool's
    /// reimplementation of a Lean predicate has drifted from Lean's, and every set
    /// below is drawn with it. Refusing is the only honest response; reporting a
    /// verdict computed with a predicate known to be wrong is not.
    fn refuse_internal_disagreement(&self) -> Result<(), String> {
        let mut disagreements = Vec::new();
        for entry in &self.census {
            if name_is_internal(&entry.name) != entry.lean_internal {
                disagreements.push(&entry.name);
            }
        }
        if disagreements.is_empty() {
            return Ok(());
        }
        let mut message = format!(
            "observation-coverage audit: this tool's reading of Lean.Name.isInternal disagrees \
             with the elaborator's on {} of the environment's {} constants, so the namespace it \
             audits is not the one the rule is about. Refusing to report a verdict. The first \
             few:\n",
            disagreements.len(),
            self.census.len()
        );
        for name in disagreements.iter().take(10) {
            let _ = writeln!(message, "  {name}");
        }
        Err(message.trim_end().to_string())
    }

    /// The record set must carry a skeleton for exactly the constants the policy
    /// needs one for, and the policy decides which those are.
    ///
    /// This is the check that closes the under-inclusion direction. The generated
    /// meta-program emits skeletons under its own condition; if that condition ever
    /// narrows -- a shape it stops recognising, a namespace test that stops
    /// matching, an empty result -- the constants it stopped emitting are still in
    /// the census, are still required here, and their absence is named. Without it a
    /// narrowing would leave the counts self-consistent and the report smaller.
    fn refuse_skeleton_mismatch(&self) -> Result<(), String> {
        let mut required: HashSet<usize> = self.vec_namespace.iter().copied().collect();
        required.extend(self.theorems.iter().copied());

        let mut absent: Vec<&str> = required
            .difference(&self.skeletons)
            .map(|index| self.census[*index].name.as_str())
            .collect();
        let mut stray: Vec<&str> = self
            .skeletons
            .difference(&required)
            .map(|index| self.census[*index].name.as_str())
            .collect();
        if absent.is_empty() && stray.is_empty() {
            return Ok(());
        }
        absent.sort_unstable();
        stray.sort_unstable();

        let mut message = format!(
            "observation-coverage audit: the fact dump carries {} type skeletons where this \
             audit's census requires {}, so the declarations it judged are not the declarations \
             the environment has. Refusing to report a verdict.\n",
            self.skeletons.len(),
            required.len()
        );
        if !absent.is_empty() {
            let _ = writeln!(
                message,
                "  {} required and not emitted, so they would have been judged against nothing:",
                absent.len()
            );
            for name in absent.iter().take(10) {
                let _ = writeln!(message, "    {name}");
            }
        }
        if !stray.is_empty() {
            let _ = writeln!(message, "  {} emitted and not required:", stray.len());
            for name in stray.iter().take(10) {
                let _ = writeln!(message, "    {name}");
            }
        }
        Err(message.trim_end().to_string())
    }

    /// An environment that cannot state the rule must not be reported against.
    ///
    /// Two ways it can fail to, and the Lean original passed both: no constants
    /// under the namespace at all, and no observation constants to write a law with.
    /// Each is a plausible accident -- a rename, a sparse checkout, a module split --
    /// and each produced "0 Vec-returning operations each carry a length law and a
    /// get? law" and status 0.
    fn refuse_missing_rule(&self) -> Result<(), String> {
        if self.vec_namespace.is_empty() {
            return Err(format!(
                "observation-coverage audit: the environment has no declarations under {VEC_NS} \
                 at all, out of {} constants, so there is nothing here to audit. Refusing to \
                 report a clean audit of an empty namespace: {} was elaborated, so check that \
                 it still declares the namespace.",
                self.census.len(),
                AUDIT_SOURCES[0]
            ));
        }
        for observation in [LENGTH_NAME, GET_NAME] {
            if !self.census.iter().any(|entry| entry.name == observation) {
                return Err(format!(
                    "observation-coverage audit: {observation} is not in the environment, so no \
                     law can be recognised and every operation would be reported as uncovered. \
                     Refusing to report against an environment that cannot state the rule."
                ));
            }
        }
        Ok(())
    }

    /// An audit that examined no operations must not report success.
    ///
    /// The third way the environment can be empty of the thing being audited, and
    /// the one that survives a namespace still carrying its observations: the bar
    /// reaches nothing. `0 Vec-returning operations each carry a length law and a
    /// get? law` and status 0 is what the original said, and it is indistinguishable
    /// from a module in perfect health.
    fn refuse_no_operations(&self, operations: usize) -> Result<(), String> {
        if operations > 0 {
            return Ok(());
        }
        Err(format!(
            "observation-coverage audit: {} declarations under {VEC_NS}, and not one of them is \
             a definition returning a Vec. Refusing to report a clean audit of no operations: \
             decision 6 is about the operations, so having none means the audit examined nothing.",
            self.vec_namespace.len()
        ))
    }

    /// An exemption naming a declaration the environment does not have excuses
    /// nothing, and the summary line goes on counting it.
    ///
    /// Renaming an exempt operation is exactly how a list like this rots, and the
    /// rot is silent: the renamed operation leaves the exemption, joins the checked
    /// set, and either passes on its laws or produces a finding nobody connects to
    /// the rename. Naming the dead entry is cheaper than either.
    fn refuse_dead_exemptions(&self) -> Result<(), String> {
        let present: HashSet<&str> = self
            .census
            .iter()
            .map(|entry| entry.name.as_str())
            .collect();
        let dead: Vec<&str> = RECURSION_OR_ALIAS
            .iter()
            .map(|(name, _)| *name)
            .filter(|name| !present.contains(name))
            .collect();
        if dead.is_empty() {
            return Ok(());
        }
        let mut message = String::from(
            "observation-coverage audit: the exemption list names declarations the environment \
             does not have, so they excuse nothing and the summary line counts them anyway. \
             Remove them, or correct the names:\n",
        );
        for name in dead {
            let _ = writeln!(message, "  {name}");
        }
        Err(message.trim_end().to_string())
    }
}

/// Read the record set into the census and the skeleton index.
///
/// The grammar is three record kinds, one per line, and their order is part of it:
/// every `K` record, then every `S` record, then the `Z` terminator.
///
/// * `K<TAB><kind><TAB><internal><TAB><name>` -- one per constant, in
///   `env.constants` order, which is what makes it a census and not a selection.
/// * `S<TAB><census index><TAB><term tokens>` -- a type skeleton.
/// * `Z<TAB><K count><TAB><S count>` -- the terminator.
///
/// The terminator is the point of the format. A Lean process killed part-way
/// through, or a disk that filled, would otherwise hand back a shorter environment
/// that parses perfectly -- and a shorter environment is a smaller audit that still
/// reports success, which is the failure this tool exists to prevent rather than
/// commit.
fn read_records(text: &str) -> Result<Audit, String> {
    let mut census: Vec<Entry> = Vec::new();
    let mut skeletons: HashSet<usize> = HashSet::new();
    let mut terminator: Option<(usize, usize)> = None;
    let mut seen_skeleton = false;

    for (offset, line) in text.lines().enumerate() {
        let line = line.strip_suffix('\r').unwrap_or(line);
        if line.is_empty() {
            continue;
        }
        let number = offset + 1;
        if terminator.is_some() {
            return Err(format!(
                "observation-coverage facts: record {number} follows the terminator: {line:?}"
            ));
        }
        let mut fields = line.split('\t');
        match fields.next() {
            Some("K") => {
                if seen_skeleton {
                    return Err(format!(
                        "observation-coverage facts: record {number} adds a constant after the \
                         first type skeleton, so the census is not complete before the audit \
                         reads it"
                    ));
                }
                let (kind, internal, name) = match (fields.next(), fields.next(), fields.next()) {
                    (Some(kind), Some(internal), Some(name)) => (kind, internal, name),
                    _ => {
                        return Err(format!(
                            "observation-coverage facts: record {number} is a census record \
                             missing a field: {line:?}"
                        ))
                    }
                };
                if fields.next().is_some() {
                    return Err(format!(
                        "observation-coverage facts: record {number} is a census record with a \
                         field too many, so a name was written unescaped: {line:?}"
                    ));
                }
                let kind = match kind {
                    "d" => Kind::Def,
                    "t" => Kind::Thm,
                    "o" => Kind::Other,
                    other => {
                        return Err(format!(
                            "observation-coverage facts: record {number} has kind {other:?}, \
                             which this tool did not write"
                        ))
                    }
                };
                let lean_internal = match internal {
                    "0" => false,
                    "1" => true,
                    other => {
                        return Err(format!(
                            "observation-coverage facts: record {number} has internal flag \
                             {other:?}, which this tool did not write"
                        ))
                    }
                };
                census.push(Entry {
                    kind,
                    lean_internal,
                    name: unescape(name).map_err(|err| {
                        format!("observation-coverage facts: record {number}: {err}")
                    })?,
                });
            }
            Some("S") => {
                seen_skeleton = true;
                let index = fields.next().ok_or_else(|| {
                    format!("observation-coverage facts: record {number} carries no census index")
                })?;
                let index: usize = index.parse().map_err(|err| {
                    format!(
                        "observation-coverage facts: record {number} has an unreadable census \
                         index: {err}"
                    )
                })?;
                if index >= census.len() {
                    return Err(format!(
                        "observation-coverage facts: record {number} is a skeleton for census \
                         index {index}, which the census does not have"
                    ));
                }
                if !skeletons.insert(index) {
                    return Err(format!(
                        "observation-coverage facts: record {number} is a second skeleton for \
                         {}",
                        census[index].name
                    ));
                }
            }
            Some("Z") => {
                let counts = (fields.next(), fields.next());
                let (constants, terms) = match counts {
                    (Some(constants), Some(terms)) => (constants, terms),
                    _ => {
                        return Err(format!(
                            "observation-coverage facts: record {number} is a terminator missing \
                             a count: {line:?}"
                        ))
                    }
                };
                let parse = |field: &str| -> Result<usize, String> {
                    field.parse::<usize>().map_err(|err| {
                        format!(
                            "observation-coverage facts: record {number} has an unreadable \
                             count: {err}"
                        )
                    })
                };
                terminator = Some((parse(constants)?, parse(terms)?));
            }
            _ => {
                return Err(format!(
                    "observation-coverage facts: record {number} is not a record this tool \
                     wrote: {line:?}"
                ))
            }
        }
    }

    match terminator {
        None => Err(
            "observation-coverage facts: the record set has no terminator, so it describes some \
             of the environment rather than all of it. Refusing to audit a namespace against a \
             partial set of laws."
                .to_string(),
        ),
        Some((constants, terms)) if constants != census.len() || terms != skeletons.len() => {
            Err(format!(
                "observation-coverage facts: the record set claims {constants} constants and \
                 {terms} type skeletons and carries {} and {}, so it was truncated in transit.",
                census.len(),
                skeletons.len()
            ))
        }
        Some(_) => {
            let vec_namespace = (0..census.len())
                .filter(|index| name_is_prefix_of(VEC_NS, &census[*index].name))
                .collect();
            let theorems = (0..census.len())
                .filter(|index| census[*index].kind == Kind::Thm)
                .collect();
            Ok(Audit {
                census,
                vec_namespace,
                theorems,
                skeletons,
            })
        }
    }
}

/// Judge the environment the record set describes.
///
/// Every set below is derived here from the census. The fact dump contributes what
/// only an elaborator knows -- the constants, their kinds, their types, the theorem
/// statements -- and decides nothing.
fn audit(text: &str) -> Result<Outcome, String> {
    let facts = read_records(text)?;
    facts.refuse_internal_disagreement()?;
    facts.refuse_skeleton_mismatch()?;
    facts.refuse_missing_rule()?;
    facts.refuse_dead_exemptions()?;

    // Pass one: the operations, and the declarations the bar does not reach.
    let mut names = NameTable::default();
    let vec_id = names.intern(VEC_NS);
    let mut operations: Vec<usize> = Vec::new();
    let mut outside_bar: Vec<usize> = Vec::new();
    for (index, tokens) in skeleton_records(text) {
        let (index, tokens) = (index?, tokens);
        let entry = &facts.census[index];
        if entry.kind != Kind::Def
            || !name_is_prefix_of(VEC_NS, &entry.name)
            || name_is_internal(&entry.name)
        {
            continue;
        }
        let skeleton = Skeleton::parse(tokens, &names)
            .map_err(|err| format!("observation-coverage facts: {}: {err}", entry.name))?;
        if skeleton.returns_vec(vec_id) {
            operations.push(index);
        } else {
            outside_bar.push(index);
        }
    }

    let exempt: HashSet<&str> = RECURSION_OR_ALIAS.iter().map(|(name, _)| *name).collect();
    let checked: Vec<usize> = operations
        .iter()
        .copied()
        .filter(|index| !exempt.contains(facts.census[*index].name.as_str()))
        .collect();
    facts.refuse_no_operations(operations.len())?;

    // Pass two: which of the checked operations any theorem in the environment
    // states a length law and a get? law for. The theorem set is the whole
    // environment's, unfiltered; a law in Lean's own library would count, which is
    // the original's behaviour and is why nothing narrows it.
    let mut names = NameTable::default();
    let eq_id = names.intern(EQ_NAME);
    let length_id = names.intern(LENGTH_NAME);
    let get_id = names.intern(GET_NAME);
    let op_ids: Vec<NameId> = checked
        .iter()
        .map(|index| names.intern(&facts.census[*index].name))
        .collect();
    let mut has_length = vec![false; checked.len()];
    let mut has_get = vec![false; checked.len()];

    for (index, tokens) in skeleton_records(text) {
        let (index, tokens) = (index?, tokens);
        let entry = &facts.census[index];
        if entry.kind != Kind::Thm {
            continue;
        }
        let skeleton = Skeleton::parse(tokens, &names)
            .map_err(|err| format!("observation-coverage facts: {}: {err}", entry.name))?;
        // A statement mentioning neither observation cannot be a law for anything,
        // and one mentioning neither operation cannot be a law about it. Both follow
        // from the predicate itself -- it requires a `Const` node for the
        // observation and one for the operation -- so this skips work rather than
        // records.
        let says_length = skeleton.mentions(length_id, 0);
        let says_get = skeleton.mentions(get_id, 0);
        if !says_length && !says_get {
            continue;
        }
        for (slot, op) in op_ids.iter().copied().enumerate() {
            if has_length[slot] && has_get[slot] {
                continue;
            }
            if !skeleton.mentions(op, 0) {
                continue;
            }
            if !has_length[slot] && says_length {
                has_length[slot] = skeleton.observes_non_vacuously(eq_id, length_id, op, 0);
            }
            if !has_get[slot] && says_get {
                has_get[slot] = skeleton.observes_non_vacuously(eq_id, get_id, op, 0);
            }
        }
    }

    let mut missing = Vec::new();
    for (slot, index) in checked.iter().enumerate() {
        let name = facts.census[*index].name.clone();
        match (has_length[slot], has_get[slot]) {
            (true, true) => {}
            (false, false) => missing.push((name, "no length law and no get? law".to_string())),
            (false, true) => missing.push((name, "no law computing its length".to_string())),
            (true, false) => missing.push((name, "no law computing its get?".to_string())),
        }
    }

    Ok(Outcome {
        operations: operations
            .iter()
            .map(|index| facts.census[*index].name.clone())
            .collect(),
        checked: checked
            .iter()
            .map(|index| facts.census[*index].name.clone())
            .collect(),
        outside_bar: outside_bar
            .iter()
            .map(|index| facts.census[*index].name.clone())
            .collect(),
        missing,
    })
}

/// Every `S` record, as `(census index, token stream)`.
///
/// A second walk of the text rather than a retained parse: the environment's ninety
/// thousand theorem statements are ninety megabytes of tokens, and the audit needs
/// each one only while it is judging it.
fn skeleton_records(text: &str) -> impl Iterator<Item = (Result<usize, String>, &str)> {
    text.lines().filter_map(|line| {
        let line = line.strip_suffix('\r').unwrap_or(line);
        let rest = line.strip_prefix("S\t")?;
        let (index, tokens) = rest.split_once('\t')?;
        Some((
            index
                .parse::<usize>()
                .map_err(|err| format!("observation-coverage facts: unreadable index: {err}")),
            tokens,
        ))
    })
}

// ---------------------------------------------------------------------------
// The fact dump.
// ---------------------------------------------------------------------------

/// A Lean string literal for `text`, so a Windows path survives being pasted into
/// generated source.
fn lean_string_literal(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

/// The generated meta-program: an unfiltered census and the type skeletons the
/// policy needs, and not one decision about the rule.
///
/// The only condition in it is which constants get a skeleton, and [`audit`]
/// recomputes that set from the census and refuses on any disagreement, so a
/// narrowing here cannot shrink the audit quietly. Everything else is a total
/// function of each constant.
fn facts_lean_source(out: &Path) -> String {
    let imports = AUDIT_IMPORTS
        .iter()
        .map(|module| format!("import {module}\n"))
        .collect::<String>();
    let out_literal = lean_string_literal(&out.to_string_lossy());
    format!(
        r#"import Lean
{imports}
open Lean

namespace GrassCoverageFacts

/-- The characters the record format reserves. -/
def needsEsc (c : Char) : Bool :=
  c == '\\' || c == '\t' || c == '\n' || c == '\r' || c == ' '

/-- One reserved character, escaped. -/
def escChar (c : Char) : String :=
  if c == '\\' then "\\\\"
  else if c == '\t' then "\\t"
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == ' ' then "\\s"
  else c.toString

/-- A field that survives the record format whatever a Name component contains. -/
def esc (s : String) : String :=
  if s.any needsEsc then s.foldl (fun acc c => acc ++ escChar c) "" else s

/--
The constructors of an `Expr`, in preorder, with the name at every constant.

Binder names, binder info, universe levels, literals and free variables are dropped:
no part of the rule reads them, and the audit's own predicates return `false` on
every leaf that is not a constant.
-/
partial def serAux (e : Expr) (acc : Array String) : Array String :=
  match e with
  | .app f a         => serAux a (serAux f (acc.push "a"))
  | .lam _ t b _     => serAux b (serAux t (acc.push "l"))
  | .forallE _ t b _ => serAux b (serAux t (acc.push "f"))
  | .letE _ t v b _  => serAux b (serAux v (serAux t (acc.push "e")))
  | .mdata _ b       => serAux b (acc.push "m")
  | .proj _ _ b      => serAux b (acc.push "p")
  | .const n _       => acc.push ("c" ++ esc (toString n))
  | _                => acc.push "x"

def ser (e : Expr) : String := String.intercalate " " (serAux e #[]).toList

/-- Which of the three `ConstantInfo` shapes the audit distinguishes this is. -/
def kindTag : ConstantInfo -> String
  | .defnInfo _ => "d"
  | .thmInfo _  => "t"
  | _           => "o"

end GrassCoverageFacts

open GrassCoverageFacts in
set_option maxHeartbeats 0 in
run_cmd do
  let env <- Elab.Command.liftCoreM getEnv
  let vecNs : Name := `Grass.Std.Logical.Vec
  let h <- IO.FS.Handle.mk {out_literal} IO.FS.Mode.write
  -- The census: every constant, in enumeration order, with nothing standing
  -- between the environment and the list.
  let mut nK : Nat := 0
  for (name, info) in env.constants.toList do
    let internal := if name.isInternal then "1" else "0"
    h.putStr ("K\t" ++ kindTag info ++ "\t" ++ internal ++ "\t" ++ esc (toString name) ++ "\n")
    nK := nK + 1
  -- The type skeletons. Which constants get one is the only condition in this
  -- file, and the caller recomputes it from the census above and refuses if the
  -- two sets differ in either direction.
  let mut nS : Nat := 0
  let mut i : Nat := 0
  for (name, info) in env.constants.toList do
    let isThm := match info with
      | .thmInfo _ => true
      | _ => false
    if vecNs.isPrefixOf name || isThm then
      h.putStr ("S\t" ++ toString i ++ "\t" ++ ser info.type ++ "\n")
      nS := nS + 1
    i := i + 1
  h.putStr ("Z\t" ++ toString nK ++ "\t" ++ toString nS ++ "\n")
"#
    )
}

/// Elaborate the generated meta-program under the repository's toolchain and read
/// back the records.
///
/// `lake env lean` is how `.github/workflows/library.yml` invoked the Lean file this
/// replaces, and it is what puts the built `.olean` files on `LEAN_PATH`; the
/// working directory therefore has to be the repository root, exactly as it did
/// before.
///
/// The record set goes to a file rather than to standard output so a Lean diagnostic
/// can never be mistaken for a fact.
fn run_facts() -> Result<String, String> {
    let dir = tempfile::Builder::new()
        .prefix("grass-coverage-facts")
        .tempdir()
        .map_err(|err| format!("could not obtain the environment facts: {err}"))?;
    let script = dir.path().join("CoverageFactsProbe.lean");
    let records = dir.path().join("records.tsv");
    fs::write(&script, facts_lean_source(&records))
        .map_err(|err| format!("could not obtain the environment facts: {err}"))?;

    let output = Command::new("lake")
        .args(["env", "lean"])
        .arg(&script)
        .output()
        .map_err(|err| format!("could not obtain the environment facts:\n{err}"))?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    if !output.status.success() {
        let combined = format!("{stdout}{}", String::from_utf8_lossy(&output.stderr));
        let capped: String = combined.trim().chars().take(2000).collect();
        return Err(format!("could not obtain the environment facts:\n{capped}"));
    }
    fs::read_to_string(&records).map_err(|err| {
        let capped: String = stdout.trim().chars().take(2000).collect();
        format!("could not obtain the environment facts ({err}):\n{capped}")
    })
}

/// The message behind this port's first deliberate departure.
///
/// A tool run from the wrong directory elaborates nothing, judges nothing, and the
/// original said so with a zero and a success line. Naming the files it looked for
/// and the directory it looked in is what turns that into a diagnosis.
fn missing_sources_message(missing: &[&str]) -> String {
    let cwd = std::env::current_dir()
        .map(|path| path.display().to_string())
        .unwrap_or_else(|err| format!("<unavailable: {err}>"));
    format!(
        "observation-coverage audit: {} not found from {cwd}, so the environment this rule is \
         about would not be elaborated.\nRefusing to report a clean audit of a tree that does \
         not carry the module: run this from the repository root.",
        missing.join(", ")
    )
}

/// The files the audit depends on, or the ones that are missing.
fn missing_sources(root: &Path) -> Vec<&'static str> {
    AUDIT_SOURCES
        .iter()
        .copied()
        .filter(|relative| !root.join(relative).is_file())
        .collect()
}

/// What the caller asked for.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mode {
    /// Judge the environment and set the exit status.
    Audit,
    /// Print the three sets the rule is drawn over and judge nothing.
    ///
    /// A diagnostic, and the thing that makes this port's equivalence against the
    /// Lean original reproducible: the summary line pins three counts, and this pins
    /// which declarations they are.
    List,
}

fn parse_args<I: IntoIterator<Item = String>>(args: I) -> Result<Mode, String> {
    let mut mode = Mode::Audit;
    for arg in args {
        match arg.as_str() {
            "--list" => mode = Mode::List,
            other => {
                return Err(format!(
                    "coverage-audit: unrecognised argument {other:?}. Usage: coverage-audit \
                     [--list]"
                ))
            }
        }
    }
    Ok(mode)
}

fn run(mode: Mode) -> Result<ExitCode, String> {
    let root = Path::new(".");
    let missing = missing_sources(root);
    if !missing.is_empty() {
        return Err(missing_sources_message(&missing));
    }

    let outcome = audit(&run_facts()?)?;

    if mode == Mode::List {
        // Sorted, because the census order is the elaborator's hash-map order:
        // stable for a given environment and meaningless to a reader diffing two.
        let mut sets = [
            ("Vec-returning operations", outcome.operations.clone()),
            ("checked", outcome.checked.clone()),
            ("outside the bar", outcome.outside_bar.clone()),
        ];
        for (label, names) in &mut sets {
            names.sort_unstable();
            println!("{label} ({}):", names.len());
            for name in names.iter() {
                println!("  {name}");
            }
        }
        println!("exempt ({}):", RECURSION_OR_ALIAS.len());
        for (name, why) in RECURSION_OR_ALIAS {
            println!("  {name}: {why}");
        }
        return Ok(ExitCode::SUCCESS);
    }

    if outcome.missing.is_empty() {
        println!("{}", outcome.success_line());
        return Ok(ExitCode::SUCCESS);
    }
    eprintln!("{}", outcome.failure_message());
    Ok(ExitCode::FAILURE)
}

fn main() -> ExitCode {
    let mode = match parse_args(std::env::args().skip(1)) {
        Ok(mode) => mode,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::FAILURE;
        }
    };
    match run(mode) {
        Ok(code) => code,
        Err(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // Fixtures.
    //
    // A record set is written the way the generated meta-program writes one, so a
    // test that changes what the audit accepts changes a record set rather than a
    // mock. `env` derives the internal flag with `name_is_internal`, so a record
    // set is consistent by construction and a test that wants a disagreement has
    // to write one.
    // -----------------------------------------------------------------------

    /// `(kind, name, type skeleton)`; an empty skeleton is not emitted at all.
    fn env(decls: &[(&str, &str, &str)]) -> String {
        let mut out = String::new();
        for (kind, name, _) in decls {
            let internal = if name_is_internal(name) { "1" } else { "0" };
            out.push_str(&format!("K\t{kind}\t{internal}\t{name}\n"));
        }
        let mut skeletons = 0usize;
        for (index, (_, _, skeleton)) in decls.iter().enumerate() {
            if skeleton.is_empty() {
                continue;
            }
            out.push_str(&format!("S\t{index}\t{skeleton}\n"));
            skeletons += 1;
        }
        out.push_str(&format!("Z\t{}\t{skeletons}\n", decls.len()));
        out
    }

    /// The declarations any environment has to carry for the rule to mean anything:
    /// the two observations, and the nine names the exemption list excuses.
    fn base() -> Vec<(&'static str, &'static str, &'static str)> {
        let mut decls = vec![("o", LENGTH_NAME, "x"), ("o", GET_NAME, "x")];
        for (name, _) in RECURSION_OR_ALIAS {
            decls.push(("o", name, "x"));
        }
        decls
    }

    /// A fixture string that outlives the record set built from it.
    fn fixed(text: String) -> &'static str {
        Box::leak(text.into_boxed_str())
    }

    /// `f arg`, as the generated meta-program writes it.
    fn call(head: &str, arg: &str) -> String {
        format!("a c{head} {arg}")
    }

    /// `@Eq _ lhs rhs`.
    fn equation(lhs: &str, rhs: &str) -> String {
        format!("a a a cEq x {lhs} {rhs}")
    }

    /// The type of a one-argument operation returning a `Vec`.
    fn vec_returning() -> String {
        format!("f a c{VEC_NS} x a c{VEC_NS} x")
    }

    /// The type of a one-argument function returning something else.
    fn not_vec_returning() -> String {
        format!("f a c{VEC_NS} x cNat")
    }

    fn length_law(op: &str) -> String {
        equation(&call(LENGTH_NAME, &call(op, "x")), "x")
    }

    fn get_law(op: &str) -> String {
        equation(&call(GET_NAME, &call(op, "x")), "x")
    }

    fn names(table: &[&str]) -> NameTable {
        let mut names = NameTable::default();
        for name in table {
            names.intern(name);
        }
        names
    }

    // -----------------------------------------------------------------------
    // Lean names.
    // -----------------------------------------------------------------------

    #[test]
    fn name_components_split_at_top_level_dots_only() {
        assert_eq!(name_components("a.b.c"), vec!["a", "b", "c"]);
        assert_eq!(
            name_components("Grass.\u{ab}Vec.probe\u{bb}"),
            vec!["Grass", "\u{ab}Vec.probe\u{bb}"]
        );
        assert_eq!(name_components("a"), vec!["a"]);
    }

    #[test]
    fn a_name_is_its_own_prefix() {
        assert!(name_is_prefix_of(VEC_NS, VEC_NS));
        assert!(name_is_prefix_of(VEC_NS, LENGTH_NAME));
    }

    #[test]
    fn the_namespace_test_is_over_components_and_not_over_characters() {
        // A flat `starts_with` would put this inside the namespace, and every
        // declaration of a `Vector` module would join the audit.
        assert!(!name_is_prefix_of(
            VEC_NS,
            "Grass.Std.Logical.Vector.length"
        ));
        // An escaped component is one component, so its interior dots are not
        // namespace boundaries.
        assert!(!name_is_prefix_of(
            VEC_NS,
            "Grass.Std.Logical.\u{ab}Vec.length\u{bb}"
        ));
        assert!(!name_is_prefix_of(VEC_NS, "Grass.Std"));
    }

    #[test]
    fn internal_names_are_the_ones_with_an_underscored_component() {
        assert!(name_is_internal("Grass.Std.Logical.Vec._sizeOf_1"));
        assert!(name_is_internal("_private.Grass.Vec.probe"));
        assert!(name_is_internal("Grass.Vec.probe._@.Grass._hyg.3"));
        assert!(!name_is_internal(LENGTH_NAME));
        // A numeric component contributes nothing of its own: Lean's `isInternal`
        // recurses past `num` rather than treating it as internal.
        assert!(!name_is_internal("Grass.Vec.probe.3"));
        // An escaped component is read on its contents.
        assert!(name_is_internal("Grass.\u{ab}_probe x\u{bb}"));
        assert!(!name_is_internal("Grass.\u{ab}probe x\u{bb}"));
    }

    // -----------------------------------------------------------------------
    // Skeletons.
    // -----------------------------------------------------------------------

    #[test]
    fn a_term_parses_into_preorder_subterm_ranges() {
        let table = names(&["f", "g"]);
        // `f (g x) x`: App(App(f, App(g, x)), x)
        let skeleton = Skeleton::parse("a a cf a cg x x", &table).expect("well formed");
        assert_eq!(skeleton.tag.len(), 7);
        assert_eq!(skeleton.end[0], 7);
        // The head of the whole application is `f`, two `app` nodes down.
        assert_eq!(skeleton.head_name(0), table.lookup("f"));
        assert_eq!(skeleton.app_args(0).len(), 2);
    }

    #[test]
    fn a_truncated_term_is_refused() {
        let table = NameTable::default();
        let err = Skeleton::parse("a a cf", &table).expect_err("not a term");
        assert!(err.contains("part-way"), "{err}");
    }

    #[test]
    fn a_term_with_a_token_too_many_is_refused() {
        let table = NameTable::default();
        let err = Skeleton::parse("x x", &table).expect_err("two terms");
        assert!(err.contains("not one term"), "{err}");
    }

    #[test]
    fn a_token_this_tool_did_not_write_is_refused() {
        let table = NameTable::default();
        assert!(Skeleton::parse("q", &table).is_err());
        assert!(Skeleton::parse("", &table).is_err());
        assert!(Skeleton::parse("aa", &table).is_err());
    }

    #[test]
    fn a_name_carrying_a_reserved_character_survives_the_token_stream() {
        let table = names(&["a b\tc\\d"]);
        let skeleton = Skeleton::parse("ca\\sb\\tc\\\\d", &table).expect("well formed");
        assert_eq!(skeleton.head_name(0), table.lookup("a b\tc\\d"));
        assert_eq!(unescape("a\\sb").unwrap(), "a b");
        assert_eq!(unescape("a\\nb\\rc").unwrap(), "a\nb\rc");
        assert!(unescape("a\\q").is_err());
        assert!(unescape("a\\").is_err());
    }

    // -----------------------------------------------------------------------
    // The three predicates, and the result-type test.
    // -----------------------------------------------------------------------

    #[test]
    fn observing_wants_the_observation_applied_to_the_operation() {
        let table = names(&[LENGTH_NAME, "op", "other"]);
        let (length, op) = (table.lookup(LENGTH_NAME), table.lookup("op"));

        let hit = Skeleton::parse(&call(LENGTH_NAME, &call("op", "x")), &table).unwrap();
        assert!(hit.observes(length, op, 0));

        // The observation applied to something else is not an observation of `op`,
        // even though `op` is in the term.
        let miss = Skeleton::parse(
            &format!(
                "l {} {}",
                call(LENGTH_NAME, &call("other", "x")),
                call("op", "x")
            ),
            &table,
        )
        .unwrap();
        assert!(!miss.observes(length, op, 0));
        assert!(miss.mentions(op, 0));
    }

    #[test]
    fn mentioning_finds_the_operation_anywhere_in_the_term() {
        let table = names(&["op"]);
        let op = table.lookup("op");
        let deep = Skeleton::parse(&format!("l x {}", call("op", "x")), &table).unwrap();
        assert!(deep.mentions(op, 0));
        let absent = Skeleton::parse("l x x", &table).unwrap();
        assert!(!absent.mentions(op, 0));
    }

    #[test]
    fn a_self_law_is_vacuous_and_does_not_count() {
        // The attack that broke the first version of this audit: an equation whose
        // two sides are the same observation of the same operation.
        let table = names(&[EQ_NAME, LENGTH_NAME, "op"]);
        let observed = call(LENGTH_NAME, &call("op", "x"));
        let skeleton = Skeleton::parse(&equation(&observed, &observed), &table).unwrap();
        assert!(!skeleton.observes_non_vacuously(
            table.lookup(EQ_NAME),
            table.lookup(LENGTH_NAME),
            table.lookup("op"),
            0
        ));
    }

    #[test]
    fn a_law_whose_other_side_is_free_of_the_operation_counts() {
        let table = names(&[EQ_NAME, LENGTH_NAME, "op"]);
        let skeleton = Skeleton::parse(&length_law("op"), &table).unwrap();
        assert!(skeleton.observes_non_vacuously(
            table.lookup(EQ_NAME),
            table.lookup(LENGTH_NAME),
            table.lookup("op"),
            0
        ));
        // And the same equation the other way round, which is the second half of
        // the original's disjunction.
        let mirrored =
            Skeleton::parse(&equation("x", &call(LENGTH_NAME, &call("op", "x"))), &table).unwrap();
        assert!(mirrored.observes_non_vacuously(
            table.lookup(EQ_NAME),
            table.lookup(LENGTH_NAME),
            table.lookup("op"),
            0
        ));
    }

    #[test]
    fn an_equation_with_the_wrong_number_of_arguments_is_not_a_law() {
        // `Eq` partially applied cannot be read as `lhs = rhs`, and the original's
        // three-element match said so.
        let table = names(&[EQ_NAME, LENGTH_NAME, "op"]);
        let partial = format!("a a cEq x {}", call(LENGTH_NAME, &call("op", "x")));
        let skeleton = Skeleton::parse(&partial, &table).unwrap();
        assert!(!skeleton.observes_non_vacuously(
            table.lookup(EQ_NAME),
            table.lookup(LENGTH_NAME),
            table.lookup("op"),
            0
        ));
    }

    #[test]
    fn a_law_nested_under_a_binder_is_found() {
        // Every real law is under the binders of its hypotheses, so the search has
        // to descend rather than look only at the statement's head.
        let table = names(&[EQ_NAME, LENGTH_NAME, "op"]);
        let under_binders = format!("f x f x {}", length_law("op"));
        let skeleton = Skeleton::parse(&under_binders, &table).unwrap();
        assert!(skeleton.observes_non_vacuously(
            table.lookup(EQ_NAME),
            table.lookup(LENGTH_NAME),
            table.lookup("op"),
            0
        ));
    }

    #[test]
    fn the_bar_is_drawn_past_the_binders() {
        let table = names(&[VEC_NS]);
        let vec = table.lookup(VEC_NS);
        assert!(Skeleton::parse(&vec_returning(), &table)
            .unwrap()
            .returns_vec(vec));
        assert!(!Skeleton::parse(&not_vec_returning(), &table)
            .unwrap()
            .returns_vec(vec));
    }

    #[test]
    fn the_bar_does_not_step_through_mdata() {
        // Inherited from the original: `returnsVec` matches `forallE` and then asks
        // `getAppFn`, which unfolds `app` and nothing else. A result type wrapped in
        // metadata is therefore outside the bar. Recorded as behaviour rather than
        // asserted as correct.
        let table = names(&[VEC_NS]);
        let wrapped = format!("f x m a c{VEC_NS} x");
        assert!(!Skeleton::parse(&wrapped, &table)
            .unwrap()
            .returns_vec(table.lookup(VEC_NS)));
    }

    // -----------------------------------------------------------------------
    // The record set.
    // -----------------------------------------------------------------------

    #[test]
    fn a_record_set_without_a_terminator_is_refused() {
        let err = read_records("K\td\t0\tFoo\n").expect_err("no terminator");
        assert!(err.contains("no terminator"), "{err}");
    }

    #[test]
    fn a_record_set_that_lost_records_in_transit_is_refused() {
        let err = read_records("K\td\t0\tFoo\nZ\t2\t0\n").expect_err("truncated");
        assert!(err.contains("truncated in transit"), "{err}");
        let err = read_records("K\td\t0\tFoo\nS\t0\tx\nZ\t1\t2\n").expect_err("truncated");
        assert!(err.contains("truncated in transit"), "{err}");
    }

    #[test]
    fn a_record_after_the_terminator_is_refused() {
        let err = read_records("K\td\t0\tFoo\nZ\t1\t0\nK\td\t0\tBar\n")
            .expect_err("record after the terminator");
        assert!(err.contains("follows the terminator"), "{err}");
    }

    #[test]
    fn a_census_record_after_a_skeleton_is_refused() {
        // The census has to be complete before the first skeleton, or a skeleton's
        // index does not name the constant the audit thinks it does.
        let err = read_records("K\td\t0\tFoo\nS\t0\tx\nK\td\t0\tBar\nZ\t2\t1\n")
            .expect_err("census reopened");
        assert!(err.contains("not complete"), "{err}");
    }

    #[test]
    fn a_record_this_tool_did_not_write_is_refused() {
        assert!(read_records("Q\tanything\nZ\t0\t0\n").is_err());
        assert!(read_records("K\tz\t0\tFoo\nZ\t1\t0\n").is_err());
        assert!(read_records("K\td\t2\tFoo\nZ\t1\t0\n").is_err());
        assert!(read_records("K\td\t0\tFoo\tBar\nZ\t1\t0\n").is_err());
        assert!(read_records("K\td\t0\nZ\t1\t0\n").is_err());
        assert!(read_records("Z\tnine\t0\n").is_err());
        assert!(read_records("Z\t0\n").is_err());
    }

    #[test]
    fn a_skeleton_for_a_constant_the_census_lacks_is_refused() {
        let err = read_records("K\td\t0\tFoo\nS\t9\tx\nZ\t1\t1\n").expect_err("no such index");
        assert!(err.contains("does not have"), "{err}");
        assert!(read_records("K\td\t0\tFoo\nS\tnine\tx\nZ\t1\t1\n").is_err());
        assert!(read_records("K\td\t0\tFoo\nS\nZ\t1\t1\n").is_err());
    }

    #[test]
    fn a_second_skeleton_for_one_constant_is_refused() {
        let err =
            read_records("K\td\t0\tFoo\nS\t0\tx\nS\t0\tx\nZ\t1\t2\n").expect_err("emitted twice");
        assert!(err.contains("second skeleton"), "{err}");
    }

    #[test]
    fn carriage_returns_and_blank_lines_do_not_change_the_record_set() {
        let plain = read_records("K\td\t0\tFoo\nZ\t1\t0\n").expect("well formed");
        let padded = read_records("K\td\t0\tFoo\r\n\r\nZ\t1\t0\r\n").expect("well formed");
        assert_eq!(plain.census.len(), padded.census.len());
        assert_eq!(plain.census[0].name, padded.census[0].name);
    }

    // -----------------------------------------------------------------------
    // The cross-checks that keep the Lean half from narrowing the audit.
    // -----------------------------------------------------------------------

    #[test]
    fn a_skeleton_the_policy_requires_and_the_dump_omits_is_refused() {
        // The direction a sibling port missed. The census still carries the
        // declaration, so the policy still asks for it, so its absence is named
        // rather than silently shrinking the set that gets judged.
        let mut decls = base();
        decls.push(("d", "Grass.Std.Logical.Vec.probe", ""));
        let err = audit(&env(&decls)).expect_err("skeleton omitted");
        assert!(err.contains("required and not emitted"), "{err}");
        assert!(err.contains("Grass.Std.Logical.Vec.probe"), "{err}");
    }

    #[test]
    fn a_theorem_the_dump_omits_is_refused_even_though_it_could_only_add_findings() {
        let mut decls = base();
        decls.push(("d", "Grass.Std.Logical.Vec.probe", fixed(vec_returning())));
        decls.push(("t", "Grass.Other.some_law", ""));
        let err = audit(&env(&decls)).expect_err("theorem omitted");
        assert!(err.contains("Grass.Other.some_law"), "{err}");
    }

    #[test]
    fn a_skeleton_the_policy_does_not_require_is_refused() {
        let mut decls = base();
        decls.push(("d", "Grass.Std.Logical.Vec.probe", fixed(vec_returning())));
        decls.push(("d", "Grass.Other.helper", "x"));
        let err = audit(&env(&decls)).expect_err("stray skeleton");
        assert!(err.contains("emitted and not required"), "{err}");
        assert!(err.contains("Grass.Other.helper"), "{err}");
    }

    #[test]
    fn an_internal_flag_this_tool_disagrees_with_is_refused() {
        // `env` derives the flag, so a disagreement has to be written by hand.
        let text = "K\td\t1\tGrass.Std.Logical.Vec.probe\nZ\t1\t0\n";
        let err = audit(text).expect_err("flags disagree");
        assert!(err.contains("isInternal"), "{err}");
        assert!(err.contains("Grass.Std.Logical.Vec.probe"), "{err}");
    }

    // -----------------------------------------------------------------------
    // The refusals that replace the original's clean audit of nothing.
    // -----------------------------------------------------------------------

    #[test]
    fn an_empty_namespace_is_refused_rather_than_reported_clean() {
        let err = audit("K\td\t0\tGrass.Other.helper\nZ\t1\t0\n").expect_err("no namespace");
        assert!(err.contains("no declarations under"), "{err}");
    }

    #[test]
    fn an_environment_that_cannot_state_the_rule_is_refused() {
        let decls = vec![
            ("o", LENGTH_NAME, "x"),
            ("d", "Grass.Std.Logical.Vec.probe", "f x cNat"),
        ];
        let err = audit(&env(&decls)).expect_err("no get?");
        assert!(err.contains(GET_NAME), "{err}");
        assert!(err.contains("cannot state the rule"), "{err}");
    }

    #[test]
    fn an_environment_with_no_operations_is_refused_rather_than_reported_clean() {
        // What the original printed here was "0 Vec-returning operations each carry
        // a length law and a get? law", with status 0.
        let mut decls = base();
        decls.push((
            "d",
            "Grass.Std.Logical.Vec.probe",
            fixed(not_vec_returning()),
        ));
        let err = audit(&env(&decls)).expect_err("nothing inside the bar");
        assert!(
            err.contains("not one of them is a definition returning a Vec"),
            "{err}"
        );
    }

    #[test]
    fn an_exemption_naming_a_declaration_the_environment_lacks_is_refused() {
        let mut decls = base();
        decls.retain(|(_, name, _)| *name != "Grass.Std.Logical.Vec.splitAt");
        decls.push(("d", "Grass.Std.Logical.Vec.probe", fixed(vec_returning())));
        let err = audit(&env(&decls)).expect_err("dead exemption");
        assert!(err.contains("Grass.Std.Logical.Vec.splitAt"), "{err}");
        assert!(err.contains("excuse nothing"), "{err}");
    }

    // -----------------------------------------------------------------------
    // The rule itself, end to end over a record set.
    // -----------------------------------------------------------------------

    /// An environment with one operation, `Vec.probe`, carrying the laws named.
    fn one_operation(laws: &[&str]) -> String {
        let mut decls = base();
        decls.push(("d", "Grass.Std.Logical.Vec.probe", fixed(vec_returning())));
        for (index, law) in laws.iter().enumerate() {
            decls.push((
                "t",
                fixed(format!("Grass.Std.Logical.Vec.law_{index}")),
                fixed(law.to_string()),
            ));
        }
        env(&decls)
    }

    #[test]
    fn an_operation_carrying_both_laws_is_clean() {
        let outcome = audit(&one_operation(&[
            &length_law("Grass.Std.Logical.Vec.probe"),
            &get_law("Grass.Std.Logical.Vec.probe"),
        ]))
        .expect("a well formed record set");
        assert!(outcome.missing.is_empty(), "{:?}", outcome.missing);
        assert_eq!(outcome.checked, vec!["Grass.Std.Logical.Vec.probe"]);
        assert_eq!(
            outcome.success_line(),
            "observation-coverage audit: 1 Vec-returning operations each carry a length law and \
             a get? law; 9 exempt by clause (ii) or the alias clause; 0 declarations outside the \
             bar's reach"
        );
    }

    #[test]
    fn an_operation_with_no_laws_is_reported() {
        let outcome = audit(&one_operation(&[])).expect("a well formed record set");
        assert_eq!(
            outcome.missing,
            vec![(
                "Grass.Std.Logical.Vec.probe".to_string(),
                "no length law and no get? law".to_string()
            )]
        );
        assert_eq!(
            outcome.failure_message(),
            "observation-coverage audit failed; docs/STDLIB.md observation coverage \
             requires a length law and a get? law for every Vec-returning operation:\n  \
             Grass.Std.Logical.Vec.probe: no length law and no get? law"
        );
    }

    #[test]
    fn an_operation_with_only_a_length_law_is_reported() {
        let outcome = audit(&one_operation(&[&length_law(
            "Grass.Std.Logical.Vec.probe",
        )]))
        .expect("a well formed record set");
        assert_eq!(outcome.missing[0].1, "no law computing its get?");
    }

    #[test]
    fn an_operation_with_only_a_get_law_is_reported() {
        let outcome = audit(&one_operation(&[&get_law("Grass.Std.Logical.Vec.probe")]))
            .expect("a well formed record set");
        assert_eq!(outcome.missing[0].1, "no law computing its length");
    }

    #[test]
    fn two_vacuous_laws_do_not_cover_an_operation() {
        let observed_length = call(LENGTH_NAME, &call("Grass.Std.Logical.Vec.probe", "x"));
        let observed_get = call(GET_NAME, &call("Grass.Std.Logical.Vec.probe", "x"));
        let outcome = audit(&one_operation(&[
            &equation(&observed_length, &observed_length),
            &equation(&observed_get, &observed_get),
        ]))
        .expect("a well formed record set");
        assert_eq!(outcome.missing[0].1, "no length law and no get? law");
    }

    #[test]
    fn a_theorem_that_mentions_the_operation_and_not_the_observation_is_not_a_law() {
        let mentions_only = equation(&call("Grass.Std.Logical.Vec.probe", "x"), "x");
        let outcome = audit(&one_operation(&[&mentions_only])).expect("a well formed record set");
        assert_eq!(outcome.missing[0].1, "no length law and no get? law");
    }

    #[test]
    fn a_law_about_one_operation_does_not_cover_another() {
        let mut decls = base();
        decls.push(("d", "Grass.Std.Logical.Vec.probe", fixed(vec_returning())));
        decls.push(("d", "Grass.Std.Logical.Vec.other", fixed(vec_returning())));
        decls.push((
            "t",
            "Grass.Std.Logical.Vec.length_probe",
            fixed(length_law("Grass.Std.Logical.Vec.probe")),
        ));
        decls.push((
            "t",
            "Grass.Std.Logical.Vec.get_probe",
            fixed(get_law("Grass.Std.Logical.Vec.probe")),
        ));
        let outcome = audit(&env(&decls)).expect("a well formed record set");
        assert_eq!(
            outcome.missing,
            vec![(
                "Grass.Std.Logical.Vec.other".to_string(),
                "no length law and no get? law".to_string()
            )]
        );
    }

    #[test]
    fn a_law_stated_outside_the_namespace_still_counts() {
        // The theorem set is the whole environment's, so a law about a `Vec`
        // operation stated anywhere covers it. Narrowing that would be the
        // fail-open direction.
        let mut decls = base();
        decls.push(("d", "Grass.Std.Logical.Vec.probe", fixed(vec_returning())));
        decls.push((
            "t",
            "Grass.Somewhere.Else.length_probe",
            fixed(length_law("Grass.Std.Logical.Vec.probe")),
        ));
        decls.push((
            "t",
            "Grass.Somewhere.Else.get_probe",
            fixed(get_law("Grass.Std.Logical.Vec.probe")),
        ));
        let outcome = audit(&env(&decls)).expect("a well formed record set");
        assert!(outcome.missing.is_empty(), "{:?}", outcome.missing);
    }

    #[test]
    fn an_exempt_operation_is_inside_the_bar_and_not_checked() {
        let mut decls = base();
        // `truncate` is on the exemption list; give it a `Vec` result and no laws.
        decls.retain(|(_, name, _)| *name != "Grass.Std.Logical.Vec.truncate");
        decls.push((
            "d",
            "Grass.Std.Logical.Vec.truncate",
            fixed(vec_returning()),
        ));
        decls.push(("d", "Grass.Std.Logical.Vec.probe", fixed(vec_returning())));
        decls.push((
            "t",
            "Grass.Std.Logical.Vec.length_probe",
            fixed(length_law("Grass.Std.Logical.Vec.probe")),
        ));
        decls.push((
            "t",
            "Grass.Std.Logical.Vec.get_probe",
            fixed(get_law("Grass.Std.Logical.Vec.probe")),
        ));
        let outcome = audit(&env(&decls)).expect("a well formed record set");
        assert!(outcome.missing.is_empty(), "{:?}", outcome.missing);
        assert_eq!(outcome.operations.len(), 2);
        assert_eq!(outcome.checked, vec!["Grass.Std.Logical.Vec.probe"]);
    }

    #[test]
    fn an_internal_declaration_is_not_an_operation() {
        let mut decls = base();
        decls.push(("d", "Grass.Std.Logical.Vec.probe", fixed(vec_returning())));
        decls.push(("d", "Grass.Std.Logical.Vec._probe", fixed(vec_returning())));
        decls.push((
            "t",
            "Grass.Std.Logical.Vec.length_probe",
            fixed(length_law("Grass.Std.Logical.Vec.probe")),
        ));
        decls.push((
            "t",
            "Grass.Std.Logical.Vec.get_probe",
            fixed(get_law("Grass.Std.Logical.Vec.probe")),
        ));
        let outcome = audit(&env(&decls)).expect("a well formed record set");
        assert_eq!(outcome.operations, vec!["Grass.Std.Logical.Vec.probe"]);
        assert!(outcome.missing.is_empty(), "{:?}", outcome.missing);
    }

    #[test]
    fn only_definitions_in_the_namespace_are_weighed() {
        let mut decls = base();
        decls.push(("d", "Grass.Std.Logical.Vec.probe", fixed(vec_returning())));
        // Outside the namespace: not an operation and not outside the bar either.
        decls.push(("d", "Grass.Other.probe", ""));
        // Inside the namespace but not a definition: skipped entirely, exactly as
        // the original's `match` skipped everything that was not `defnInfo`.
        decls.push(("o", "Grass.Std.Logical.Vec.Probe", "x"));
        // Inside the namespace, a definition, outside the bar.
        decls.push((
            "d",
            "Grass.Std.Logical.Vec.probeSize",
            fixed(not_vec_returning()),
        ));
        let outcome = audit(&env(&decls)).expect("a well formed record set");
        assert_eq!(outcome.operations, vec!["Grass.Std.Logical.Vec.probe"]);
        assert_eq!(outcome.outside_bar, vec!["Grass.Std.Logical.Vec.probeSize"]);
    }

    #[test]
    fn findings_are_reported_in_census_order() {
        let mut decls = base();
        decls.push(("d", "Grass.Std.Logical.Vec.zeta", fixed(vec_returning())));
        decls.push(("d", "Grass.Std.Logical.Vec.alpha", fixed(vec_returning())));
        let outcome = audit(&env(&decls)).expect("a well formed record set");
        assert_eq!(
            outcome
                .missing
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>(),
            vec!["Grass.Std.Logical.Vec.zeta", "Grass.Std.Logical.Vec.alpha"]
        );
    }

    // -----------------------------------------------------------------------
    // The generated meta-program, and the command line.
    // -----------------------------------------------------------------------

    #[test]
    fn the_generated_source_elaborates_the_modules_the_rule_is_about() {
        let source = facts_lean_source(Path::new("out.tsv"));
        for module in AUDIT_IMPORTS {
            assert!(source.contains(&format!("import {module}\n")), "{module}");
        }
        // The census is unfiltered, and the audit's cross-check depends on it
        // being written before the first skeleton.
        let census = source.find("\"K\\t\"").expect("a census record");
        let skeleton = source.find("\"S\\t\"").expect("a skeleton record");
        assert!(census < skeleton, "{source}");
    }

    #[test]
    fn a_windows_path_survives_becoming_a_lean_literal() {
        assert_eq!(
            lean_string_literal("C:\\Users\\x\\records.tsv"),
            "\"C:\\\\Users\\\\x\\\\records.tsv\""
        );
        let source = facts_lean_source(Path::new("C:\\t\\records.tsv"));
        assert!(source.contains("\"C:\\\\t\\\\records.tsv\""), "{source}");
    }

    #[test]
    fn the_command_line_is_the_audit_or_the_listing() {
        assert_eq!(parse_args(Vec::<String>::new()).unwrap(), Mode::Audit);
        assert_eq!(parse_args(vec!["--list".to_string()]).unwrap(), Mode::List);
        let err = parse_args(vec!["--verbose".to_string()]).expect_err("not an argument");
        assert!(err.contains("--list"), "{err}");
    }

    #[test]
    fn a_tree_without_the_module_is_named_along_with_the_directory() {
        let dir = tempfile::tempdir().expect("a temporary directory");
        let missing = missing_sources(dir.path());
        assert_eq!(missing, AUDIT_SOURCES.to_vec());
        let message = missing_sources_message(&missing);
        for source in AUDIT_SOURCES {
            assert!(message.contains(source), "{message}");
        }
        assert!(message.contains("repository root"), "{message}");
    }

    #[test]
    fn a_tree_that_carries_the_modules_is_not_refused() {
        let dir = tempfile::tempdir().expect("a temporary directory");
        for source in AUDIT_SOURCES {
            let path = dir.path().join(source);
            fs::create_dir_all(path.parent().expect("a parent")).expect("a directory");
            fs::write(&path, "-- fixture\n").expect("a file");
        }
        assert!(missing_sources(dir.path()).is_empty());
    }
}
