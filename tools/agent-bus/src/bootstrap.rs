//! `_bus/BUS.json`, the immutable bootstrap file (AGENT_BUS.md section 2,
//! AGENT_BUS_SCHEMA.md section 2).

use crate::error::{invalid, AbResult};
use crate::scalars::{Agent, EventId, ObjectId, StringSet};
use serde::{Deserialize, Serialize};

pub const SUPPORTED_MERGE_ENGINE: &str = "git-ort";
/// The exact `git` version this helper was validated against for candidate
/// construction (`git merge-tree --write-tree`, ORT strategy). Bootstrap
/// refuses to run against a different version, per AGENT_BUS_SCHEMA.md section 2.
pub const SUPPORTED_MERGE_ENGINE_VERSION: &str = "2.53.0";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BusJson {
    pub v: u32,
    pub object_format: String,
    pub coordinators: StringSet<Agent>,
    pub product_review_from: ObjectId,
    pub merge_engine: String,
    pub merge_engine_version: String,
    pub merge_engine_epoch: EventId,
}

impl BusJson {
    pub fn new(
        object_format: String,
        coordinators: Vec<Agent>,
        product_review_from: ObjectId,
    ) -> AbResult<BusJson> {
        if object_format != "sha1" && object_format != "sha256" {
            return Err(invalid(format!("unsupported object_format: {object_format}")));
        }
        if coordinators.is_empty() {
            return Err(invalid("bootstrap requires at least one coordinator"));
        }
        let coordinators = StringSet::from_iter(coordinators);
        let epoch_agent = coordinators
            .iter()
            .next()
            .expect("checked nonempty above")
            .clone();
        let installed = crate::gitrepo::version()?;
        if installed != SUPPORTED_MERGE_ENGINE_VERSION {
            return Err(invalid(format!(
                "installed git {installed} does not match the pinned merge engine version {SUPPORTED_MERGE_ENGINE_VERSION}; bootstrap refuses to run"
            )));
        }
        Ok(BusJson {
            v: crate::envelope::SCHEMA_VERSION,
            object_format,
            coordinators,
            product_review_from,
            merge_engine: SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: SUPPORTED_MERGE_ENGINE_VERSION.to_string(),
            merge_engine_epoch: EventId::new(&epoch_agent, 0),
        })
    }

    pub fn parse(bytes: &[u8]) -> AbResult<BusJson> {
        let text = std::str::from_utf8(bytes).map_err(|e| invalid(format!("BUS.json not UTF-8: {e}")))?;
        if !text.ends_with('\n') || text.matches('\n').count() != 1 {
            return Err(invalid("BUS.json must be exactly one line plus LF"));
        }
        let line = &text[..text.len() - 1];
        let value: serde_json::Value = serde_json::from_str(line)?;
        let known = [
            "v",
            "object_format",
            "coordinators",
            "product_review_from",
            "merge_engine",
            "merge_engine_version",
            "merge_engine_epoch",
        ];
        if let serde_json::Value::Object(map) = &value {
            for k in map.keys() {
                if !known.contains(&k.as_str()) {
                    return Err(invalid(format!("unknown BUS.json field: {k}")));
                }
            }
        } else {
            return Err(invalid("BUS.json is not a JSON object"));
        }
        crate::canon::check_nfc(&value)?;
        let bus: BusJson = serde_json::from_value(value)?;
        if bus.v != crate::envelope::SCHEMA_VERSION {
            return Err(invalid(format!("unsupported BUS.json schema version {}", bus.v)));
        }
        if bus.object_format != "sha1" && bus.object_format != "sha256" {
            return Err(invalid(format!("unsupported object_format: {}", bus.object_format)));
        }
        if bus.coordinators.is_empty() {
            return Err(invalid("coordinators must be nonempty"));
        }
        if bus.merge_engine != SUPPORTED_MERGE_ENGINE {
            return Err(invalid(format!(
                "unsupported merge_engine: {}",
                bus.merge_engine
            )));
        }
        if !bus.coordinators.iter().any(|c| c == &bus.merge_engine_epoch.agent()) || bus.merge_engine_epoch.seq() != 0
        {
            return Err(invalid(
                "merge_engine_epoch must name a bootstrap coordinator's sequence-zero registration",
            ));
        }
        let canonical = serde_json::to_string(&bus)?;
        if canonical != line {
            return Err(invalid("BUS.json is not canonically encoded"));
        }
        if bus.product_review_from.as_str().len() != bus.object_id_len() {
            return Err(invalid(format!(
                "product_review_from length does not match object_format {}",
                bus.object_format
            )));
        }
        Ok(bus)
    }

    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        let mut s = serde_json::to_string(self).expect("serializable");
        s.push('\n');
        s.into_bytes()
    }

    pub fn object_id_len(&self) -> usize {
        ObjectId::expected_len(&self.object_format).unwrap_or(40)
    }
}

pub const GITATTRIBUTES_CONTENTS: &str = "*.jsonl -text\n";
