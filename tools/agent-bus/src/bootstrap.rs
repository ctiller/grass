//! The bus-wide configuration fixed at version-two activation
//! (docs/AGENT_COORDINATION_EVOLUTION.md section 2.5): the product object
//! format, the exact product commit migration started from, and the pinned
//! merge engine. Unlike version one's single immutable `_bus/BUS.json`, this
//! is not a standalone commit of its own -- it's established alongside the
//! registry's root epoch (`registry.rs`), since activation and the first
//! roster epoch are one atomic act. There is deliberately no `coordinators`
//! list here: coordinator authority is `Role::Coordinator` membership in the
//! registry's current epoch, not a separate immutable roster.

use crate::error::{invalid, AbResult};
use crate::scalars::ObjectId;
use serde::{Deserialize, Serialize};

pub const SUPPORTED_MERGE_ENGINE: &str = "git-ort";
/// The exact `git` version this helper was validated against for candidate
/// construction (`git merge-tree --write-tree`, ORT strategy). Activation
/// refuses to run against a different version.
pub const SUPPORTED_MERGE_ENGINE_VERSION: &str = "2.53.0";

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct BusConfig {
    pub object_format: String,
    pub product_review_from: ObjectId,
    pub merge_engine: String,
    pub merge_engine_version: String,
}

impl BusConfig {
    pub fn new(object_format: String, product_review_from: ObjectId) -> AbResult<BusConfig> {
        if object_format != "sha1" && object_format != "sha256" {
            return Err(invalid(format!(
                "unsupported object_format: {object_format}"
            )));
        }
        let installed = crate::gitrepo::version()?;
        if installed != SUPPORTED_MERGE_ENGINE_VERSION {
            return Err(invalid(format!(
                "installed git {installed} does not match the pinned merge engine version \
                 {SUPPORTED_MERGE_ENGINE_VERSION}; activation refuses to run"
            )));
        }
        Ok(BusConfig {
            object_format,
            product_review_from,
            merge_engine: SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: SUPPORTED_MERGE_ENGINE_VERSION.to_string(),
        })
    }

    pub fn object_id_len(&self) -> usize {
        ObjectId::expected_len(&self.object_format).unwrap_or(40)
    }

    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        let value = serde_json::to_value(self).expect("BusConfig always serializable");
        serde_json::to_vec(&value).expect("BusConfig value always serializable")
    }

    pub fn parse(bytes: &[u8]) -> AbResult<BusConfig> {
        let config: BusConfig = serde_json::from_slice(bytes)
            .map_err(|e| invalid(format!("malformed bus config: {e}")))?;
        if config.object_format != "sha1" && config.object_format != "sha256" {
            return Err(invalid(format!(
                "unsupported object_format: {}",
                config.object_format
            )));
        }
        if config.merge_engine != SUPPORTED_MERGE_ENGINE {
            return Err(invalid(format!(
                "unsupported merge_engine: {}",
                config.merge_engine
            )));
        }
        if config.product_review_from.as_str().len() != config.object_id_len() {
            return Err(invalid(format!(
                "product_review_from length does not match object_format {}",
                config.object_format
            )));
        }
        Ok(config)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn oid(n: u64) -> ObjectId {
        ObjectId::parse(format!("{n:040x}")).unwrap()
    }

    #[test]
    fn to_canonical_bytes_round_trips_through_parse() {
        let config = BusConfig {
            object_format: "sha1".to_string(),
            product_review_from: oid(1),
            merge_engine: SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: SUPPORTED_MERGE_ENGINE_VERSION.to_string(),
        };
        let bytes = config.to_canonical_bytes();
        let parsed = BusConfig::parse(&bytes).unwrap();
        assert_eq!(parsed, config);
    }

    #[test]
    fn parse_rejects_an_unsupported_object_format() {
        let value = serde_json::json!({
            "object_format": "sha512",
            "product_review_from": oid(1).as_str(),
            "merge_engine": SUPPORTED_MERGE_ENGINE,
            "merge_engine_version": SUPPORTED_MERGE_ENGINE_VERSION,
        });
        let err = BusConfig::parse(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(err.to_string().contains("unsupported object_format"), "{err}");
    }

    #[test]
    fn parse_rejects_an_unsupported_merge_engine() {
        let value = serde_json::json!({
            "object_format": "sha1",
            "product_review_from": oid(1).as_str(),
            "merge_engine": "recursive",
            "merge_engine_version": SUPPORTED_MERGE_ENGINE_VERSION,
        });
        let err = BusConfig::parse(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(err.to_string().contains("unsupported merge_engine"), "{err}");
    }

    #[test]
    fn parse_rejects_a_product_review_from_of_the_wrong_length_for_its_object_format() {
        let value = serde_json::json!({
            "object_format": "sha256",
            "product_review_from": oid(1).as_str(), // 40 hex chars, sha256 wants 64
            "merge_engine": SUPPORTED_MERGE_ENGINE,
            "merge_engine_version": SUPPORTED_MERGE_ENGINE_VERSION,
        });
        let err = BusConfig::parse(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(
            err.to_string().contains("product_review_from length"),
            "{err}"
        );
    }
}
