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

/// Creates a v2-native genesis from nothing: the registry's root epoch,
/// naming `coordinator` as its sole `Role::Coordinator` member, and that
/// coordinator's own stream root (its `agent.registered` event, sequence
/// zero). There is genuinely nothing to observe yet, so that event's
/// frontier is empty rather than complete -- the v2 analogue of v1's
/// "`observed` is `null` only for the bootstrap coordinator's first
/// `agent.registered` event."
///
/// This is deliberately the v2-native path only: an actual v1-fleet
/// migration (docs/AGENT_COORDINATION_EVOLUTION.md section 2.5 --
/// replaying v1's existing bus history, computing each identity's
/// `final_v1_seq`, creating every existing agent's stream root as a
/// continuation) is a distinct, later concern with its own module once this
/// rewrite is otherwise ready to cut over; nothing here depends on it.
#[allow(clippy::too_many_arguments)]
pub fn genesis(
    repo: &std::path::Path,
    coordinator: &crate::scalars::Agent,
    display_name: crate::scalars::Short,
    purpose: crate::scalars::Text,
    object_format: String,
    product_review_from: ObjectId,
    host: crate::scalars::Short,
    worktrees_dir: &std::path::Path,
) -> AbResult<(BusConfig, crate::registry::RosterEpoch, ObjectId)> {
    let config = BusConfig::new(object_format, product_review_from)?;

    let mut members = std::collections::BTreeMap::new();
    members.insert(
        coordinator.clone(),
        crate::registry::MemberBinding {
            role: crate::events::Role::Coordinator,
            host,
            coordinator_custody_epoch: 0,
        },
    );
    let epoch = crate::registry::create_root(repo, members, &worktrees_dir.join("_registry_root"))?;

    let header = crate::stream::StreamHeader {
        agent: coordinator.clone(),
        activation_event: None,
        registration_authority: crate::scalars::EventId::new(coordinator, 0),
        final_v1_seq: None,
        object_format: config.object_format.clone(),
        schema_fingerprint: SCHEMA_FINGERPRINT.to_string(),
    };
    let data = crate::events::EventData::AgentRegistered(crate::events::AgentRegistered {
        display_name,
        primary_role: crate::events::Role::Coordinator,
        purpose,
        product_base: None,
        product_branch: None,
        provider: None,
        model: None,
    });
    let observed = crate::frontier::ObservedFrontier::sparse(epoch.id.clone(), []);
    let first_event = crate::envelope::Envelope::new(coordinator, 0, observed, &data, []);
    let commit = crate::stream::create_root_commit(
        repo,
        &header,
        &first_event,
        &worktrees_dir.join(format!("_stream_root_{coordinator}")),
    )?;
    Ok((config, epoch, commit))
}

/// A fingerprint of the v2 schema this build implements, printed by
/// `agent-bus --version` and carried in every stream header -- a reader can
/// detect a schema mismatch without fully parsing content built against a
/// different revision.
pub const SCHEMA_FINGERPRINT: &str = "agent-bus-v2-schema-1";

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

    fn init_repo() -> tempfile::TempDir {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path();
        std::process::Command::new("git")
            .args(["init", "--quiet", "-b", "main"])
            .arg(path)
            .status()
            .unwrap();
        for args in [
            vec!["config", "user.email", "test@example.com"],
            vec!["config", "user.name", "Test"],
        ] {
            std::process::Command::new("git")
                .arg("-C")
                .arg(path)
                .args(args)
                .status()
                .unwrap();
        }
        std::fs::write(path.join("README.md"), "hello\n").unwrap();
        std::process::Command::new("git")
            .arg("-C")
            .arg(path)
            .args(["add", "README.md"])
            .status()
            .unwrap();
        std::process::Command::new("git")
            .arg("-C")
            .arg(path)
            .args(["commit", "-q", "-m", "initial"])
            .status()
            .unwrap();
        dir
    }

    #[test]
    fn genesis_creates_a_registry_root_and_the_coordinators_own_stream() {
        let repo = init_repo();
        let coord1 = crate::scalars::Agent::parse("coord1".to_string()).unwrap();
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        let (config, epoch, first_commit) = genesis(
            repo.path(),
            &coord1,
            crate::scalars::Short::parse("Coordinator One".to_string()).unwrap(),
            crate::scalars::Text::parse("bootstraps the fleet".to_string()).unwrap(),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            crate::scalars::Short::parse("host1".to_string()).unwrap(),
            &repo.path().join("_worktrees"),
        )
        .unwrap();

        assert_eq!(config.object_format, "sha1");
        assert!(epoch.is_active_member(&coord1));
        assert_eq!(
            crate::registry::read_registry_tip(repo.path()).unwrap(),
            Some(epoch.id)
        );
        assert_eq!(
            crate::stream::read_stream_tip(repo.path(), &coord1).unwrap(),
            Some(first_commit)
        );

        let reads_dir = repo.path().join("_reads");
        let (header, log) = crate::stream::read_stream(repo.path(), &coord1, &reads_dir).unwrap();
        assert_eq!(
            header.registration_authority,
            crate::scalars::EventId::new(&coord1, 0)
        );
        assert_eq!(header.activation_event, None);
        assert_eq!(log.len(), 1);
        assert_eq!(log[0].kind, "agent.registered");
    }
}
