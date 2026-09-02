//! The version-1 event envelope (AGENT_BUS.md section 5, AGENT_BUS_SCHEMA.md section 2).
//!
//! Field declaration order below is load-bearing: serde_json serializes a Rust
//! struct's fields in declaration order (not alphabetically), which is how we
//! satisfy the fixed envelope field order without a bespoke writer. `data` is
//! always built via `serde_json::to_value` on a typed payload, which routes
//! through `serde_json::Map` (a `BTreeMap` since we do not enable the
//! `preserve_order` feature) and therefore comes out with lexicographically
//! sorted keys "for free".

use crate::error::{invalid, AbResult};
use crate::events::EventData;
use crate::scalars::{Agent, EventId, ObjectId, StringSet, Timestamp};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

pub const SCHEMA_VERSION: u32 = 1;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Envelope {
    pub v: u32,
    pub id: EventId,
    pub agent: Agent,
    pub seq: u64,
    pub time: Timestamp,
    pub observed: Option<ObjectId>,
    pub kind: String,
    pub refs: StringSet<EventId>,
    pub data: serde_json::Value,
}

impl Envelope {
    pub fn new(
        agent: &Agent,
        seq: u64,
        observed: Option<ObjectId>,
        data: &EventData,
        extra_refs: impl IntoIterator<Item = EventId>,
    ) -> Envelope {
        let mut refs: BTreeSet<EventId> = data.referenced_ids();
        refs.extend(extra_refs);
        Envelope {
            v: SCHEMA_VERSION,
            id: EventId::new(agent, seq),
            agent: agent.clone(),
            seq,
            time: Timestamp::now_utc(),
            observed,
            kind: data.kind().to_string(),
            refs: StringSet::from_iter(refs),
            data: data.to_value(),
        }
    }

    /// Parse and structurally validate one JSONL line's envelope shape.
    /// This does NOT perform semantic/authority validation (see `validate.rs`).
    pub fn parse_line(line: &str) -> AbResult<Envelope> {
        let value: serde_json::Value = serde_json::from_str(line)?;
        let env: Envelope = serde_json::from_value(value.clone())
            .map_err(|e| invalid(format!("malformed envelope: {e}")))?;

        // Canonical form: re-serializing the typed struct reproduces the
        // fixed top-level field order (declaration order) with the `data`
        // sub-object already alphabetically sorted (it round-tripped through
        // `serde_json::Value`, whose `Map` is a `BTreeMap`), compactly, with
        // minimal escaping. Byte-identity with the original line is exactly
        // AGENT_BUS_SCHEMA.md section 2's canonical-encoding requirement.
        if env.to_canonical_line() != line {
            return Err(invalid(format!(
                "{}: line is not canonically encoded",
                env.id
            )));
        }
        crate::canon::check_nfc(&env.data)?;

        // id/agent/seq agreement.
        if env.id.agent() != env.agent {
            return Err(invalid(format!(
                "id agent {} does not match agent field {}",
                env.id.agent(),
                env.agent
            )));
        }
        if env.id.seq() != env.seq {
            return Err(invalid(format!(
                "id seq {} does not match seq field {}",
                env.id.seq(),
                env.seq
            )));
        }
        if env.v != SCHEMA_VERSION {
            return Err(invalid(format!("unsupported schema version {}", env.v)));
        }

        // Unknown top-level envelope fields.
        if let serde_json::Value::Object(map) = &value {
            let known = [
                "v", "id", "agent", "seq", "time", "observed", "kind", "refs", "data",
            ];
            for k in map.keys() {
                if !known.contains(&k.as_str()) {
                    return Err(invalid(format!("unknown envelope field: {k}")));
                }
            }
        } else {
            return Err(invalid("event line is not a JSON object"));
        }

        // Typed data payload + refs agreement.
        let data = EventData::from_kind_and_value(&env.kind, env.data.clone())?;
        let expected: BTreeSet<EventId> = data.referenced_ids();
        let actual: BTreeSet<EventId> = env.refs.iter().cloned().collect();
        if expected != actual {
            return Err(invalid(format!(
                "refs mismatch for {}: envelope has {:?}, data references {:?}",
                env.id, actual, expected
            )));
        }

        Ok(env)
    }

    pub fn typed_data(&self) -> AbResult<EventData> {
        EventData::from_kind_and_value(&self.kind, self.data.clone())
    }

    pub fn to_canonical_line(&self) -> String {
        serde_json::to_string(self).expect("envelope always serializable")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::events::{AgentResumed, AgentStatusEvent, LifecycleStatus};
    use crate::scalars::EventId;

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn hash(n: u64) -> String {
        format!("{n:040x}")
    }

    fn oid(n: u64) -> ObjectId {
        ObjectId::parse(hash(n)).unwrap()
    }

    fn status_data() -> EventData {
        EventData::AgentStatus(AgentStatusEvent {
            status: LifecycleStatus::Active,
            note: crate::scalars::Text::parse("".into()).unwrap(),
            product_branch: None,
            product_commit: None,
        })
    }

    fn resumed_data(previous: &EventId) -> EventData {
        EventData::AgentResumed(AgentResumed {
            previous_lifecycle: previous.clone(),
            reason: crate::scalars::Text::parse("r".into()).unwrap(),
            user_authority: crate::scalars::Text::parse("u".into()).unwrap(),
        })
    }

    /// A canonically-encoded line round-trips through `parse_line` cleanly.
    #[test]
    fn parse_line_accepts_a_canonical_line() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, Some(oid(1)), &data, []);
        let line = e.to_canonical_line();
        let parsed = Envelope::parse_line(&line).expect("a canonical line must parse");
        assert_eq!(parsed.id, e.id);
    }

    /// Insignificant whitespace still parses as valid JSON but is not
    /// byte-identical to the canonical re-serialization, so it must be
    /// rejected as not canonically encoded (AGENT_BUS_SCHEMA.md section 2).
    #[test]
    fn parse_line_rejects_noncanonical_whitespace() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, Some(oid(1)), &data, []);
        let canonical = e.to_canonical_line();
        let padded = canonical.replacen('{', "{ ", 1);
        assert_ne!(padded, canonical);
        let err = Envelope::parse_line(&padded).unwrap_err();
        assert!(err.to_string().contains("not canonically encoded"), "{err}");
    }

    /// `id`'s embedded agent must agree with the top-level `agent` field.
    #[test]
    fn parse_line_rejects_id_agent_mismatch() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, Some(oid(1)), &data, []);
        let canonical = e.to_canonical_line();
        let needle = "\"agent\":\"alice\"";
        assert!(canonical.contains(needle), "{canonical}");
        let tampered = canonical.replacen(needle, "\"agent\":\"mallory\"", 1);
        let err = Envelope::parse_line(&tampered).unwrap_err();
        assert!(
            err.to_string().contains("does not match agent field"),
            "{err}"
        );
    }

    /// `id`'s embedded seq must agree with the top-level `seq` field.
    #[test]
    fn parse_line_rejects_id_seq_mismatch() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, Some(oid(1)), &data, []);
        let canonical = e.to_canonical_line();
        let needle = "\"seq\":0,";
        assert!(canonical.contains(needle), "{canonical}");
        let tampered = canonical.replacen(needle, "\"seq\":1,", 1);
        let err = Envelope::parse_line(&tampered).unwrap_err();
        assert!(
            err.to_string().contains("does not match seq field"),
            "{err}"
        );
    }

    /// Only schema version 1 is currently supported.
    #[test]
    fn parse_line_rejects_unsupported_schema_version() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, Some(oid(1)), &data, []);
        let canonical = e.to_canonical_line();
        let needle = "\"v\":1,";
        assert!(canonical.contains(needle), "{canonical}");
        let tampered = canonical.replacen(needle, "\"v\":2,", 1);
        let err = Envelope::parse_line(&tampered).unwrap_err();
        assert!(
            err.to_string().contains("unsupported schema version"),
            "{err}"
        );
    }

    /// `refs` must equal exactly the event IDs the typed `data` references
    /// (AGENT_BUS_SCHEMA.md section 2); a hand-tampered `refs` that drops the
    /// one id `AgentResumed.previous_lifecycle` requires must be rejected.
    #[test]
    fn parse_line_rejects_refs_mismatch() {
        let alice = a("alice");
        let prev = EventId::new(&alice, 3);
        let data = resumed_data(&prev);
        let e = Envelope::new(&alice, 4, Some(oid(1)), &data, []);
        let canonical = e.to_canonical_line();
        let needle = format!("\"refs\":[\"{prev}\"]");
        assert!(canonical.contains(&needle), "{canonical}");
        let tampered = canonical.replacen(&needle, "\"refs\":[]", 1);
        let err = Envelope::parse_line(&tampered).unwrap_err();
        assert!(err.to_string().contains("refs mismatch"), "{err}");
    }

    /// Malformed top-level JSON (not even an object) fails at the initial
    /// typed-deserialize step with a "malformed envelope" error; `parse_line`'s
    /// own later `else` branch for "not a JSON object" is unreachable through
    /// this function because `Envelope`'s required fields can only ever
    /// deserialize successfully from a JSON object in the first place.
    #[test]
    fn parse_line_rejects_non_object_json_at_the_typed_deserialize_step() {
        let err = Envelope::parse_line("[1,2,3]").unwrap_err();
        assert!(err.to_string().contains("malformed envelope"), "{err}");
    }

    /// An unknown top-level field is dropped silently by `Envelope`'s
    /// `Deserialize` (it has no `deny_unknown_fields`), so the extra bytes
    /// always desynchronize the canonical-encoding check first; the explicit
    /// "unknown envelope field" loop later in `parse_line` is consequently
    /// unreachable through this function today. This test documents that
    /// actual, observed behavior rather than the field's own (currently dead)
    /// error message.
    #[test]
    fn parse_line_extra_top_level_field_is_caught_by_the_canonical_check_first() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, Some(oid(1)), &data, []);
        let canonical = e.to_canonical_line();
        let tampered = canonical.replacen('{', "{\"surprise\":true,", 1);
        let err = Envelope::parse_line(&tampered).unwrap_err();
        assert!(err.to_string().contains("not canonically encoded"), "{err}");
    }
}
