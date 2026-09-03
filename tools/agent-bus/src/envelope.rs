//! The version-two event envelope
//! (docs/AGENT_COORDINATION_EVOLUTION.md sections 2.1-2.2).
//!
//! Replaces version one's `observed: Option<ObjectId>` (a single whole-bus
//! branch commit) with a full `ObservedFrontier`: there is no global bus-head
//! commit in version two, so an event's causal position is a per-agent map
//! from identity to an exact stream commit and the last event ID consumed
//! from it. Every other envelope-shaping rule from version one carries
//! forward unchanged: fixed field declaration order (relied on for the
//! canonical encoding), `data` built via `serde_json::to_value` (routes
//! through a `BTreeMap`-backed `serde_json::Map`, so object keys sort "for
//! free"), and `refs` must equal exactly the event IDs the typed `data`
//! references.

use crate::error::{invalid, AbResult};
use crate::events::EventData;
use crate::frontier::ObservedFrontier;
use crate::scalars::{Agent, EventId, StringSet, Timestamp};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

pub const SCHEMA_VERSION: u32 = 2;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Envelope {
    pub v: u32,
    pub id: EventId,
    pub agent: Agent,
    pub seq: u64,
    pub time: Timestamp,
    pub observed: ObservedFrontier,
    pub kind: String,
    pub refs: StringSet<EventId>,
    pub data: serde_json::Value,
}

impl Envelope {
    pub fn new(
        agent: &Agent,
        seq: u64,
        observed: ObservedFrontier,
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

    /// Parse and structurally validate one JSONL line's envelope shape. This
    /// does NOT perform semantic/authority validation (frontier-vs-registry
    /// completeness, stream custody, lifecycle rules) -- see `frontier.rs`
    /// and the (forthcoming) stream/coordinator validation layer for that.
    pub fn parse_line(line: &str) -> AbResult<Envelope> {
        let value: serde_json::Value = serde_json::from_str(line)?;
        let env: Envelope = serde_json::from_value(value.clone())
            .map_err(|e| invalid(format!("malformed envelope: {e}")))?;

        if env.to_canonical_line() != line {
            return Err(invalid(format!(
                "{}: line is not canonically encoded",
                env.id
            )));
        }
        crate::canon::check_nfc(&env.data)?;

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

        let data = EventData::from_kind_and_value(&env.kind, env.data.clone())?;
        let expected: BTreeSet<EventId> = data.referenced_ids();
        let actual: BTreeSet<EventId> = env.refs.iter().cloned().collect();
        if expected != actual {
            return Err(invalid(format!(
                "refs mismatch for {}: envelope has {:?}, data references {:?}",
                env.id, actual, expected
            )));
        }

        // Gate 4: every cross-agent reference must occur at or before the
        // referenced agent's declared frontier position. A same-agent
        // reference (to the author's own earlier event) needs no frontier
        // entry -- it is checked against the stream's own contiguous
        // sequence by the stream-replay layer, not here.
        for r in env.refs.iter() {
            if r.agent() != env.agent {
                env.observed.validate_reference(r)?;
            }
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
    use crate::frontier::FrontierEntry;
    use crate::scalars::{EventId, ObjectId};

    fn a(name: &str) -> Agent {
        Agent::parse(name.to_string()).unwrap()
    }

    fn hash(n: u64) -> String {
        format!("{n:040x}")
    }

    fn oid(n: u64) -> ObjectId {
        ObjectId::parse(hash(n)).unwrap()
    }

    fn empty_frontier() -> ObservedFrontier {
        ObservedFrontier::sparse(oid(1), [])
    }

    fn frontier_seeing(id: &EventId, tip: u64) -> ObservedFrontier {
        ObservedFrontier::sparse(
            oid(1),
            [FrontierEntry {
                agent: id.agent(),
                stream_tip: oid(tip),
                through: id.clone(),
            }],
        )
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

    #[test]
    fn parse_line_accepts_a_canonical_line() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, empty_frontier(), &data, []);
        let line = e.to_canonical_line();
        let parsed = Envelope::parse_line(&line).expect("a canonical line must parse");
        assert_eq!(parsed.id, e.id);
    }

    #[test]
    fn parse_line_rejects_noncanonical_whitespace() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, empty_frontier(), &data, []);
        let canonical = e.to_canonical_line();
        let padded = canonical.replacen('{', "{ ", 1);
        assert_ne!(padded, canonical);
        let err = Envelope::parse_line(&padded).unwrap_err();
        assert!(err.to_string().contains("not canonically encoded"), "{err}");
    }

    #[test]
    fn parse_line_rejects_id_agent_mismatch() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, empty_frontier(), &data, []);
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

    #[test]
    fn parse_line_rejects_id_seq_mismatch() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, empty_frontier(), &data, []);
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

    #[test]
    fn parse_line_rejects_unsupported_schema_version() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, empty_frontier(), &data, []);
        let canonical = e.to_canonical_line();
        let needle = "\"v\":2,";
        assert!(canonical.contains(needle), "{canonical}");
        let tampered = canonical.replacen(needle, "\"v\":1,", 1);
        let err = Envelope::parse_line(&tampered).unwrap_err();
        assert!(
            err.to_string().contains("unsupported schema version"),
            "{err}"
        );
    }

    #[test]
    fn parse_line_rejects_refs_mismatch() {
        let alice = a("alice");
        let prev = EventId::new(&alice, 3);
        let data = resumed_data(&prev);
        let e = Envelope::new(&alice, 4, frontier_seeing(&prev, 1), &data, []);
        let canonical = e.to_canonical_line();
        let needle = format!("\"refs\":[\"{prev}\"]");
        assert!(canonical.contains(&needle), "{canonical}");
        let tampered = canonical.replacen(&needle, "\"refs\":[]", 1);
        let err = Envelope::parse_line(&tampered).unwrap_err();
        assert!(err.to_string().contains("refs mismatch"), "{err}");
    }

    #[test]
    fn parse_line_rejects_non_object_json_at_the_typed_deserialize_step() {
        let err = Envelope::parse_line("[1,2,3]").unwrap_err();
        assert!(err.to_string().contains("malformed envelope"), "{err}");
    }

    #[test]
    fn parse_line_extra_top_level_field_is_caught_by_the_canonical_check_first() {
        let alice = a("alice");
        let data = status_data();
        let e = Envelope::new(&alice, 0, empty_frontier(), &data, []);
        let canonical = e.to_canonical_line();
        let tampered = canonical.replacen('{', "{\"surprise\":true,", 1);
        let err = Envelope::parse_line(&tampered).unwrap_err();
        assert!(err.to_string().contains("not canonically encoded"), "{err}");
    }

    /// Gate 4, positive case: a cross-agent reference at exactly the
    /// declared frontier position is accepted.
    #[test]
    fn parse_line_accepts_a_cross_agent_reference_within_the_frontier() {
        let alice = a("alice");
        let bob_prev = EventId::new(&a("bob"), 2);
        let data = resumed_data(&bob_prev);
        let e = Envelope::new(&alice, 0, frontier_seeing(&bob_prev, 7), &data, []);
        let line = e.to_canonical_line();
        assert!(Envelope::parse_line(&line).is_ok());
    }

    /// Gate 4, negative case: a cross-agent reference past the declared
    /// frontier position must be rejected at parse time, not silently
    /// accepted because the referenced ID happens to be well-formed.
    #[test]
    fn parse_line_rejects_a_cross_agent_reference_outside_the_frontier() {
        let alice = a("alice");
        let bob = a("bob");
        let bob_ahead = EventId::new(&bob, 5);
        let data = resumed_data(&bob_ahead);
        // Frontier only knows bob through seq 2, but the event references
        // bob:5 -- past what was declared observed.
        let stale_frontier = frontier_seeing(&EventId::new(&bob, 2), 7);
        let e = Envelope::new(&alice, 0, stale_frontier, &data, []);
        let line = e.to_canonical_line();
        let err = Envelope::parse_line(&line).unwrap_err();
        assert!(err.to_string().contains("occurs after"), "{err}");
    }

    /// A same-agent self-reference needs no frontier entry at all -- it must
    /// not be rejected merely because the frontier is silent about the
    /// author's own stream.
    #[test]
    fn parse_line_does_not_require_a_frontier_entry_for_a_same_agent_reference() {
        let alice = a("alice");
        let prev = EventId::new(&alice, 3);
        let data = resumed_data(&prev);
        // Deliberately empty frontier: same-agent causality follows the
        // stream's own sequence, not the frontier.
        let e = Envelope::new(&alice, 4, empty_frontier(), &data, []);
        let line = e.to_canonical_line();
        assert!(Envelope::parse_line(&line).is_ok());
    }
}
