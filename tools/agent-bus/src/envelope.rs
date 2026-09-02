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
            return Err(invalid(format!("{}: line is not canonically encoded", env.id)));
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
            let known = ["v", "id", "agent", "seq", "time", "observed", "kind", "refs", "data"];
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
