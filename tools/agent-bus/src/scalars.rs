//! Validated scalar and collection types shared across the schema: agent
//! identities, event ids, git object ids, timestamps, refs, and the bounded
//! text fields event payloads are built from. Every type here is a thin,
//! validated wrapper over `String` (or a `Vec` for sets), transparently
//! (de)serialized as its underlying JSON representation, so a malformed
//! value can never silently enter a typed struct -- it fails to parse.

#![allow(dead_code)]

use crate::error::{invalid, AbResult};
use serde::de::Error as DeError;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;

/// A newtype over `String` with a validated grammar, transparently
/// (de)serialized as a JSON string.
macro_rules! validated_string {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(String);

        impl $name {
            pub fn as_str(&self) -> &str {
                &self.0
            }
            pub fn into_string(self) -> String {
                self.0
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl AsRef<str> for $name {
            fn as_ref(&self) -> &str {
                &self.0
            }
        }

        impl Serialize for $name {
            fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                s.serialize_str(&self.0)
            }
        }

        impl<'de> Deserialize<'de> for $name {
            fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
                let raw = String::deserialize(d)?;
                $name::parse(raw).map_err(DeError::custom)
            }
        }
    };
}

validated_string!(Agent, "Agent identity name: `[a-z][a-z0-9-]{0,47}`.");

impl Agent {
    pub fn parse(s: String) -> AbResult<Self> {
        let re = regex::Regex::new(r"^[a-z][a-z0-9-]{0,47}$").unwrap();
        if !re.is_match(&s) {
            return Err(invalid(format!("invalid agent name: {s:?}")));
        }
        Ok(Agent(s))
    }

    /// Names beginning with `_` are reserved for the helper's own use
    /// (operational state, not a real identity) -- the grammar above already
    /// excludes them, but a caller assembling a name from untrusted parts
    /// before validating benefits from a direct check too.
    pub fn is_reserved(s: &str) -> bool {
        s.starts_with('_')
    }
}

validated_string!(
    EventId,
    "`<Agent>:<seq>`, where `seq` is a canonical (no leading zero) `u64`."
);

impl EventId {
    pub fn parse(s: String) -> AbResult<Self> {
        let (agent, seq) = s
            .split_once(':')
            .ok_or_else(|| invalid(format!("malformed event id: {s:?}")))?;
        Agent::parse(agent.to_string())?;
        if seq.is_empty()
            || (seq != "0" && seq.starts_with('0'))
            || !seq.chars().all(|c| c.is_ascii_digit())
        {
            return Err(invalid(format!("malformed event id sequence: {s:?}")));
        }
        seq.parse::<u64>()
            .map_err(|_| invalid(format!("event id sequence out of range: {s:?}")))?;
        Ok(EventId(s))
    }

    pub fn new(agent: &Agent, seq: u64) -> Self {
        EventId(format!("{agent}:{seq}"))
    }

    pub fn agent(&self) -> Agent {
        let (a, _) = self.0.split_once(':').expect("grammar guarantees a colon");
        Agent(a.to_string())
    }

    pub fn seq(&self) -> u64 {
        let (_, s) = self.0.split_once(':').expect("grammar guarantees a colon");
        s.parse().expect("grammar guarantees a valid u64")
    }
}

validated_string!(
    ObjectId,
    "Lowercase hexadecimal full git object id (sha1: 40 hex, sha256: 64 hex)."
);

impl ObjectId {
    pub fn parse(s: String) -> AbResult<Self> {
        let ok_len = s.len() == 40 || s.len() == 64;
        if !ok_len
            || !s
                .chars()
                .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
        {
            return Err(invalid(format!("invalid object id: {s:?}")));
        }
        Ok(ObjectId(s))
    }

    pub fn expected_len(object_format: &str) -> Option<usize> {
        match object_format {
            "sha1" => Some(40),
            "sha256" => Some(64),
            _ => None,
        }
    }
}

validated_string!(
    Timestamp,
    "UTC `YYYY-MM-DDTHH:MM:SSZ`, no fractional seconds."
);

impl Timestamp {
    pub fn parse(s: String) -> AbResult<Self> {
        let re = regex::Regex::new(r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z$").unwrap();
        if !re.is_match(&s) {
            return Err(invalid(format!("invalid timestamp: {s:?}")));
        }
        let fmt = time::format_description::well_known::Rfc3339;
        time::OffsetDateTime::parse(&s, &fmt)
            .map_err(|e| invalid(format!("invalid timestamp {s:?}: {e}")))?;
        Ok(Timestamp(s))
    }

    pub fn now_utc() -> Self {
        let now = time::OffsetDateTime::now_utc();
        Timestamp(format!(
            "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z",
            now.year(),
            u8::from(now.month()),
            now.day(),
            now.hour(),
            now.minute(),
            now.second()
        ))
    }
}

validated_string!(Branch, "A full ref accepted by `git check-ref-format`.");

impl Branch {
    /// Syntactic validation approximating `git check-ref-format --normalize`,
    /// then confirmed against the real `git check-ref-format` -- every
    /// deployment of this tool already hard-depends on a `git` binary, so
    /// this adds no new external dependency.
    pub fn parse(s: String) -> AbResult<Self> {
        if !s.starts_with("refs/") {
            return Err(invalid(format!("branch must start with refs/: {s:?}")));
        }
        if s.is_empty()
            || s.starts_with('/')
            || s.ends_with('/')
            || s.contains("//")
            || s.contains("..")
            || s.contains(' ')
            || s.contains('~')
            || s.contains('^')
            || s.contains(':')
            || s.contains('?')
            || s.contains('*')
            || s.contains('[')
            || s.contains('\\')
            || s.ends_with(".lock")
            || s.ends_with('.')
            || s.chars().any(|c| c.is_control())
        {
            return Err(invalid(format!("invalid ref syntax: {s:?}")));
        }
        for component in s.split('/') {
            if component.is_empty() || component.starts_with('.') || component.ends_with(".lock") {
                return Err(invalid(format!("invalid ref component in {s:?}")));
            }
        }
        if !crate::gitrepo::check_ref_format(&s) {
            return Err(invalid(format!("git check-ref-format rejects {s:?}")));
        }
        Ok(Branch(s))
    }

    pub fn is_product_branch_for(&self, agent: &Agent) -> bool {
        let prefix = format!("refs/heads/agent/{agent}/");
        if let Some(topic) = self.0.strip_prefix(&prefix) {
            Topic::parse(topic.to_string()).is_ok()
        } else {
            false
        }
    }
}

validated_string!(
    Topic,
    "Lowercase alphanumeric/hyphen, begins/ends alphanumeric, length 1..64."
);

impl Topic {
    pub fn parse(s: String) -> AbResult<Self> {
        let re = regex::Regex::new(r"^[a-z0-9]([a-z0-9-]{0,62}[a-z0-9])?$").unwrap();
        if s.is_empty() || s.len() > 64 || !re.is_match(&s) {
            return Err(invalid(format!("invalid topic: {s:?}")));
        }
        Ok(Topic(s))
    }
}

validated_string!(
    PathClaim,
    "Repo-relative exact path, or a directory prefix ending `/**`."
);

impl PathClaim {
    /// Only one glob-like construct is permitted at all: one literal
    /// trailing `/**`. Any other glob character (`*`, `?`, `[`, `]`) --
    /// including inside that trailing component itself, e.g. `a/**/b` -- is
    /// rejected, since `overlaps` below treats the string as a plain
    /// prefix/exact match and a real glob would silently match nothing.
    pub fn parse(s: String) -> AbResult<Self> {
        if s.is_empty() || s.starts_with('/') || (s.ends_with('/') && !s.ends_with("/**")) {
            return Err(invalid(format!("invalid path claim: {s:?}")));
        }
        let stripped = s.strip_suffix("/**").unwrap_or(&s);
        if stripped.is_empty() {
            return Err(invalid(format!("invalid path claim: {s:?}")));
        }
        for component in stripped.split('/') {
            if component.is_empty() || component == "." || component == ".." {
                return Err(invalid(format!("invalid path claim component in {s:?}")));
            }
        }
        if s.contains('\\') || stripped.contains(['*', '?', '[', ']']) {
            return Err(invalid(format!(
                "path claim contains an unsupported character or glob: {s:?}"
            )));
        }
        Ok(PathClaim(s))
    }

    pub fn overlaps(&self, other: &PathClaim) -> bool {
        fn as_prefix(p: &str) -> Option<&str> {
            p.strip_suffix("/**")
        }
        match (as_prefix(&self.0), as_prefix(&other.0)) {
            (Some(a), Some(b)) => {
                a == b || a.starts_with(&format!("{b}/")) || b.starts_with(&format!("{a}/"))
            }
            (Some(a), None) => other.0 == a || other.0.starts_with(&format!("{a}/")),
            (None, Some(b)) => self.0 == b || self.0.starts_with(&format!("{b}/")),
            (None, None) => self.0 == other.0,
        }
    }
}

validated_string!(Short, "UTF-8 string of 1..256 bytes after JSON decoding.");

impl Short {
    pub fn parse(s: String) -> AbResult<Self> {
        let n = s.len();
        if !(1..=256).contains(&n) {
            return Err(invalid(format!("Short out of bounds ({n} bytes): {s:?}")));
        }
        Ok(Short(s))
    }
}

validated_string!(Text, "UTF-8 string of 0..4096 bytes after JSON decoding.");

impl Text {
    pub fn parse(s: String) -> AbResult<Self> {
        let n = s.len();
        if n > 4096 {
            return Err(invalid(format!("Text out of bounds ({n} bytes)")));
        }
        Ok(Text(s))
    }
}

/// JSON array of unique `T`, byte-lexicographically sorted by
/// `T::as_ref::<str>()`. Rejects an unsorted or duplicate-containing array
/// at deserialize time rather than silently normalizing it, so a
/// hand-crafted payload can never disagree with its own canonical encoding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringSet<T>(Vec<T>);

pub const MAX_ARRAY_LEN: usize = 256;

impl<T> StringSet<T> {
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
    pub fn as_slice(&self) -> &[T] {
        &self.0
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<T: AsRef<str> + Ord> StringSet<T> {
    pub fn build(mut v: Vec<T>) -> Self {
        v.sort_by(|a, b| a.as_ref().cmp(b.as_ref()));
        v.dedup_by(|a, b| a.as_ref() == b.as_ref());
        StringSet(v)
    }

    fn check_sorted(v: &[T]) -> AbResult<()> {
        for w in v.windows(2) {
            match w[0].as_ref().cmp(w[1].as_ref()) {
                std::cmp::Ordering::Less => {}
                std::cmp::Ordering::Equal => {
                    return Err(invalid(format!("duplicate set member: {}", w[0].as_ref())))
                }
                std::cmp::Ordering::Greater => {
                    return Err(invalid("set members not byte-lexicographically sorted"))
                }
            }
        }
        Ok(())
    }
}

impl<T> Default for StringSet<T> {
    fn default() -> Self {
        StringSet(Vec::new())
    }
}

impl<T: Serialize> Serialize for StringSet<T> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(s)
    }
}

impl<'de, T: Deserialize<'de> + AsRef<str> + Ord> Deserialize<'de> for StringSet<T> {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let v: Vec<T> = Vec::deserialize(d)?;
        if v.len() > MAX_ARRAY_LEN {
            return Err(DeError::custom(format!(
                "array has {} members, exceeding the {MAX_ARRAY_LEN} bound",
                v.len()
            )));
        }
        StringSet::<T>::check_sorted(&v).map_err(DeError::custom)?;
        Ok(StringSet(v))
    }
}

impl<T> FromIterator<T> for StringSet<T>
where
    T: AsRef<str> + Ord,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        StringSet::build(iter.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn agent_grammar() {
        assert!(Agent::parse("alice".into()).is_ok());
        assert!(Agent::parse("alice-2".into()).is_ok());
        assert!(Agent::parse("Alice".into()).is_err());
        assert!(Agent::parse("2alice".into()).is_err());
        assert!(Agent::parse("_reserved".into()).is_err());
        assert!(Agent::is_reserved("_reserved"));
    }

    #[test]
    fn event_id_roundtrip() {
        let a = Agent::parse("alice".into()).unwrap();
        let id = EventId::new(&a, 17);
        assert_eq!(id.as_str(), "alice:17");
        assert_eq!(id.agent(), a);
        assert_eq!(id.seq(), 17);
        assert!(
            EventId::parse("alice:017".into()).is_err(),
            "leading zero must be rejected"
        );
        assert!(EventId::parse("alice:".into()).is_err());
    }

    #[test]
    fn object_id_grammar() {
        assert!(ObjectId::parse("a".repeat(40)).is_ok());
        assert!(ObjectId::parse("a".repeat(64)).is_ok());
        assert!(ObjectId::parse("a".repeat(41)).is_err());
        assert!(ObjectId::parse("A".repeat(40)).is_err());
        assert_eq!(ObjectId::expected_len("sha1"), Some(40));
        assert_eq!(ObjectId::expected_len("sha256"), Some(64));
        assert_eq!(ObjectId::expected_len("nonsense"), None);
    }

    #[test]
    fn timestamp_grammar() {
        assert!(Timestamp::parse("2026-09-02T12:00:00Z".into()).is_ok());
        assert!(Timestamp::parse("2026-02-30T12:00:00Z".into()).is_err());
        assert!(Timestamp::parse("2026-09-02T12:00:00".into()).is_err());
        let now = Timestamp::now_utc();
        assert!(Timestamp::parse(now.into_string()).is_ok());
    }

    #[test]
    fn path_claim_overlap() {
        let a = PathClaim::parse("Grass/Instruction/X86/**".into()).unwrap();
        let b = PathClaim::parse("Grass/Instruction/X86/Encoder.lean".into()).unwrap();
        let c = PathClaim::parse("Grass/Instruction/Arm/**".into()).unwrap();
        assert!(a.overlaps(&b));
        assert!(!a.overlaps(&c));
        assert!(a.overlaps(&a));
    }

    #[test]
    fn path_claim_rejects_a_glob_character() {
        assert!(PathClaim::parse("a/*/b".into()).is_err());
        assert!(PathClaim::parse("a/**/b".into()).is_err());
    }

    #[test]
    fn string_set_rejects_unsorted_or_duplicate() {
        let v: Result<StringSet<Agent>, _> = serde_json::from_str(r#"["bob","alice"]"#);
        assert!(v.is_err());
        let v: Result<StringSet<Agent>, _> = serde_json::from_str(r#"["alice","alice"]"#);
        assert!(v.is_err());
        let v: Result<StringSet<Agent>, _> = serde_json::from_str(r#"["alice","bob"]"#);
        assert!(v.is_ok());
    }

    #[test]
    fn string_set_from_iter_sorts_and_dedupes() {
        let a = Agent::parse("alice".into()).unwrap();
        let b = Agent::parse("bob".into()).unwrap();
        let set = StringSet::from_iter([b.clone(), a.clone(), a.clone()]);
        assert_eq!(set.as_slice(), &[a, b]);
    }

    #[test]
    fn branch_requires_refs_prefix_and_valid_syntax() {
        assert!(Branch::parse("main".into()).is_err());
        assert!(Branch::parse("refs/heads/main".into()).is_ok());
        assert!(Branch::parse("refs/heads/../etc".into()).is_err());
    }

    #[test]
    fn branch_is_product_branch_for_matches_topic_under_agent_prefix() {
        let alice = Agent::parse("alice".into()).unwrap();
        let b = Branch::parse("refs/heads/agent/alice/feature".into()).unwrap();
        assert!(b.is_product_branch_for(&alice));
        let bob = Agent::parse("bob".into()).unwrap();
        assert!(!b.is_product_branch_for(&bob));
    }
}
