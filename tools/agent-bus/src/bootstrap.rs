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

#[cfg(test)]
mod tests {
    use super::*;

    fn coord() -> Agent {
        Agent::parse("coord1".to_string()).unwrap()
    }

    fn hash(n: u64) -> String {
        format!("{n:040x}")
    }

    fn hash256(n: u64) -> String {
        format!("{n:064x}")
    }

    // ---------------------------------------------------------------- new()

    #[test]
    fn new_rejects_unsupported_object_format() {
        let err = BusJson::new("sha3".to_string(), vec![coord()], ObjectId::parse(hash(1)).unwrap()).unwrap_err();
        assert!(err.to_string().contains("unsupported object_format"), "{err}");
    }

    #[test]
    fn new_rejects_empty_coordinators() {
        let err = BusJson::new("sha1".to_string(), vec![], ObjectId::parse(hash(1)).unwrap()).unwrap_err();
        assert!(err.to_string().contains("at least one coordinator"), "{err}");
    }

    #[test]
    fn new_builds_sha256_bus_json_with_first_coordinator_as_epoch_agent() {
        // Coordinators are sorted by `StringSet::from_iter`, so "abby" (not the
        // first argument) ends up first and must own the merge_engine_epoch.
        let abby = Agent::parse("abby".to_string()).unwrap();
        let bus = BusJson::new("sha256".to_string(), vec![coord(), abby.clone()], ObjectId::parse(hash256(1)).unwrap())
            .unwrap();
        assert_eq!(bus.object_format, "sha256");
        assert_eq!(bus.merge_engine_epoch, EventId::new(&abby, 0));
        assert_eq!(bus.object_id_len(), 64);
    }

    // -------------------------------------------------------------- parse()

    fn valid_bus() -> BusJson {
        BusJson::new("sha1".to_string(), vec![coord()], ObjectId::parse(hash(1)).unwrap()).unwrap()
    }

    #[test]
    fn parse_roundtrips_canonical_bytes() {
        let bus = valid_bus();
        let bytes = bus.to_canonical_bytes();
        let parsed = BusJson::parse(&bytes).unwrap();
        assert_eq!(parsed.object_format, bus.object_format);
        assert_eq!(parsed.coordinators.as_slice(), bus.coordinators.as_slice());
        assert_eq!(parsed.merge_engine_epoch, bus.merge_engine_epoch);
    }

    #[test]
    fn parse_rejects_non_utf8() {
        let err = BusJson::parse(&[0xff, 0xfe, 0xfd]).unwrap_err();
        assert!(err.to_string().contains("not UTF-8"), "{err}");
    }

    #[test]
    fn parse_rejects_missing_trailing_newline() {
        let bytes = valid_bus().to_canonical_bytes();
        let mut without_nl = bytes.clone();
        without_nl.pop();
        let err = BusJson::parse(&without_nl).unwrap_err();
        assert!(err.to_string().contains("exactly one line"), "{err}");
    }

    #[test]
    fn parse_rejects_multiple_lines() {
        let mut bytes = valid_bus().to_canonical_bytes();
        bytes.extend_from_slice(b"trailing garbage\n");
        let err = BusJson::parse(&bytes).unwrap_err();
        assert!(err.to_string().contains("exactly one line"), "{err}");
    }

    #[test]
    fn parse_rejects_non_object_json() {
        let err = BusJson::parse(b"[]\n").unwrap_err();
        assert!(err.to_string().contains("not a JSON object"), "{err}");
    }

    #[test]
    fn parse_rejects_unknown_field() {
        let mut line = serde_json::to_value(valid_bus()).unwrap();
        line["extra"] = serde_json::json!("nope");
        let bytes = format!("{}\n", serde_json::to_string(&line).unwrap()).into_bytes();
        let err = BusJson::parse(&bytes).unwrap_err();
        assert!(err.to_string().contains("unknown BUS.json field"), "{err}");
    }

    #[test]
    fn parse_rejects_wrong_schema_version() {
        let mut line = serde_json::to_value(valid_bus()).unwrap();
        line["v"] = serde_json::json!(9999);
        // Bypass canonical-encoding rejection by keeping keys in the same
        // serialized order `serde_json::to_string` would produce for a `Value`
        // built from `to_value` (field order is preserved from the struct).
        let bytes = format!("{}\n", serde_json::to_string(&line).unwrap()).into_bytes();
        let err = BusJson::parse(&bytes).unwrap_err();
        assert!(err.to_string().contains("unsupported BUS.json schema version"), "{err}");
    }

    #[test]
    fn parse_rejects_unsupported_object_format() {
        let mut line = serde_json::to_value(valid_bus()).unwrap();
        line["object_format"] = serde_json::json!("sha3");
        let bytes = format!("{}\n", serde_json::to_string(&line).unwrap()).into_bytes();
        let err = BusJson::parse(&bytes).unwrap_err();
        assert!(err.to_string().contains("unsupported object_format"), "{err}");
    }

    #[test]
    fn parse_rejects_empty_coordinators() {
        let mut line = serde_json::to_value(valid_bus()).unwrap();
        line["coordinators"] = serde_json::json!([]);
        let bytes = format!("{}\n", serde_json::to_string(&line).unwrap()).into_bytes();
        let err = BusJson::parse(&bytes).unwrap_err();
        assert!(err.to_string().contains("coordinators must be nonempty"), "{err}");
    }

    #[test]
    fn parse_rejects_unsupported_merge_engine() {
        let mut line = serde_json::to_value(valid_bus()).unwrap();
        line["merge_engine"] = serde_json::json!("some-other-engine");
        let bytes = format!("{}\n", serde_json::to_string(&line).unwrap()).into_bytes();
        let err = BusJson::parse(&bytes).unwrap_err();
        assert!(err.to_string().contains("unsupported merge_engine"), "{err}");
    }

    #[test]
    fn parse_rejects_epoch_not_naming_a_bootstrap_coordinator() {
        let mut line = serde_json::to_value(valid_bus()).unwrap();
        line["merge_engine_epoch"] = serde_json::json!("someone-else:0");
        let bytes = format!("{}\n", serde_json::to_string(&line).unwrap()).into_bytes();
        let err = BusJson::parse(&bytes).unwrap_err();
        assert!(
            err.to_string().contains("must name a bootstrap coordinator's sequence-zero registration"),
            "{err}"
        );
    }

    #[test]
    fn parse_rejects_epoch_with_nonzero_seq() {
        let mut line = serde_json::to_value(valid_bus()).unwrap();
        line["merge_engine_epoch"] = serde_json::json!("coord1:1");
        let bytes = format!("{}\n", serde_json::to_string(&line).unwrap()).into_bytes();
        let err = BusJson::parse(&bytes).unwrap_err();
        assert!(
            err.to_string().contains("must name a bootstrap coordinator's sequence-zero registration"),
            "{err}"
        );
    }

    #[test]
    fn parse_rejects_noncanonical_encoding() {
        // Same fields, different (non-canonical) key order.
        let bus = valid_bus();
        let canonical = serde_json::to_string(&bus).unwrap();
        let value: serde_json::Value = serde_json::from_str(&canonical).unwrap();
        let obj = value.as_object().unwrap();
        // Rebuild as a JSON object literal with keys in reverse order.
        let mut reordered = serde_json::Map::new();
        for (k, v) in obj.iter().rev() {
            reordered.insert(k.clone(), v.clone());
        }
        let line = format!("{}\n", serde_json::to_string(&serde_json::Value::Object(reordered)).unwrap());
        let err = BusJson::parse(line.as_bytes()).unwrap_err();
        assert!(err.to_string().contains("not canonically encoded"), "{err}");
    }

    #[test]
    fn parse_rejects_object_id_length_mismatch_for_declared_format() {
        // The object_id_len check runs only after the canonical-encoding check,
        // so build this by string-substituting inside an already-canonical
        // line (rather than mutating a `Value`, whose key order is alphabetic
        // and would trip the earlier canonical check first): sha1 format
        // declared, but product_review_from is a sha256-length hex id.
        let canonical = String::from_utf8(valid_bus().to_canonical_bytes()).unwrap();
        assert!(canonical.contains(&hash(1)));
        let line = canonical.replace(&hash(1), &hash256(1));
        let err = BusJson::parse(line.as_bytes()).unwrap_err();
        assert!(err.to_string().contains("product_review_from length does not match object_format"), "{err}");
    }

    #[test]
    fn object_id_len_defaults_to_40_for_unrecognized_format() {
        // `object_id_len` is only reachable with a format `parse`/`new` already
        // validated as sha1/sha256, but its `unwrap_or(40)` fallback is still
        // directly exercisable and worth pinning down.
        let mut bus = valid_bus();
        bus.object_format = "unknown".to_string();
        assert_eq!(bus.object_id_len(), 40);
    }

    #[test]
    fn gitattributes_contents_is_the_expected_single_line() {
        assert_eq!(GITATTRIBUTES_CONTENTS, "*.jsonl -text\n");
    }
}
