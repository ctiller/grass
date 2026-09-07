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
        if object_format != "sha1" {
            return Err(invalid(format!(
                "unsupported object_format: {object_format} -- the vendored libgit2 this crate \
                 reads objects through (src/gitobjects.rs) only supports sha1 without its \
                 experimental sha256 build flag; activation refuses to publish a bus no reader \
                 could ever open"
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
        if config.object_format != "sha1" {
            return Err(invalid(format!(
                "unsupported object_format: {} -- the vendored libgit2 this crate reads objects \
                 through (src/gitobjects.rs) only supports sha1 without its experimental sha256 \
                 build flag",
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

/// AGENT_REVIEW.md section 7 requires candidate construction to use "the merge
/// engine and exact version pinned in immutable `BUS.json` **or the currently
/// selected `merge_engine.activated` epoch**", and section 12's fixture 13
/// requires rejecting "candidate construction with an unpinned merge engine or
/// helper options".
///
/// Both authorities matter, and reading only the first is worse than reading
/// neither. `BusConfig::new` enforces the pin at *activation*, on whichever
/// host activated, and `BusConfig::parse` checks only the engine name -- so
/// every host afterwards could build candidates with whatever `git` it had.
/// But a bus that later moves to a new engine version does so precisely by
/// publishing `merge_engine.activated`; checking the frozen bootstrap value
/// would then reject every host running the currently selected engine, and
/// section 7's own upgrade mechanism would become the thing that permanently
/// disables merging. The selected epoch therefore wins when one exists, and
/// the bootstrap config is the fallback for a bus that has never upgraded.
///
/// Deliberately not the compile-time [`SUPPORTED_MERGE_ENGINE_VERSION`]: the
/// authority is the bus's, not this binary's, so a bus pinned to an older git
/// keeps rejecting a newer host even when this binary was built expecting the
/// newer one.
pub(crate) fn require_pinned_merge_engine(state: &crate::state::BusState) -> AbResult<()> {
    let (engine, version) = match state
        .current_merge_engine_epoch
        .as_ref()
        .and_then(|epoch| state.merge_engine_info.get(epoch))
    {
        Some((engine, version)) => (engine.as_str().to_string(), version.as_str().to_string()),
        None => (
            state.config.merge_engine.clone(),
            state.config.merge_engine_version.clone(),
        ),
    };
    if engine != SUPPORTED_MERGE_ENGINE {
        return Err(invalid(format!(
            "this bus selects merge engine {engine}, which this helper cannot run"
        )));
    }
    let installed = crate::gitrepo::version()?;
    if installed != version {
        return Err(invalid(format!(
            "installed git {installed} is not the merge engine version this bus selects ({version}); candidate construction refuses to run, because a tree built by a different engine version cannot be reconstructed by the hosts that must verify it"
        )));
    }
    Ok(())
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
///
/// Safely resumable across a crash between its two commits (section 2.5:
/// "define recovery for a partially created registry or stream set"). If
/// the registry root already exists, this checks it was created by this
/// exact call (same config, same sole coordinator member) before treating
/// it as a resume point -- a genuinely different prior activation, or one
/// that has already moved past its root epoch, is refused rather than
/// silently adopted. If the coordinator's own stream root is also already
/// there, this is a pure idempotent no-op returning the existing commit.
#[allow(clippy::too_many_arguments)]
pub fn genesis(
    repo: &std::path::Path,
    coordinator: &crate::scalars::Agent,
    display_name: crate::scalars::Short,
    purpose: crate::scalars::Text,
    object_format: String,
    product_review_from: ObjectId,
    host: crate::scalars::Short,
) -> AbResult<(BusConfig, crate::registry::RosterEpoch, ObjectId)> {
    let config = BusConfig::new(object_format, product_review_from)?;

    let epoch = match crate::registry::read_registry_tip(repo)? {
        Some(tip) => {
            let existing = crate::registry::read_epoch(repo, &tip)?;
            let existing_config = crate::registry::read_bus_config(repo, &tip)?;
            let sole_coordinator = existing.active_members.len() == 1
                && existing
                    .active_members
                    .get(coordinator)
                    .is_some_and(|b| b.role == crate::events::Role::Coordinator && b.host == host);
            if existing.parent.is_some() || existing_config != config || !sole_coordinator {
                return Err(invalid(
                    "the agent-registry already has a root epoch that does not match this \
                     genesis call -- this bus was already activated (possibly differently); \
                     use `register` to add a further agent instead of `genesis`",
                ));
            }
            existing
        }
        None => {
            let mut members = std::collections::BTreeMap::new();
            members.insert(
                coordinator.clone(),
                crate::registry::MemberBinding {
                    role: crate::events::Role::Coordinator,
                    host,
                    coordinator_custody_epoch: 0,
                    standby: None,
                },
            );
            crate::registry::create_root(repo, &config, members)?
        }
    };

    if let Some(existing_tip) = crate::stream::read_stream_tip(repo, coordinator)? {
        // Resuming across a crash between the two commits genesis makes
        // must not silently accept a *different* display_name/purpose than
        // what this call would have written -- the epoch-mismatch check
        // above only covers the first commit's content, so without this the
        // second commit's content could diverge from the caller's current
        // arguments without ever being noticed.
        let (_, log) = crate::stream::read_stream(repo, coordinator)?;
        let first = log
            .first()
            .ok_or_else(|| invalid(format!("{coordinator}'s stream exists but has no events")))?;
        let crate::events::EventData::AgentRegistered(existing) = first.typed_data()? else {
            return Err(invalid(format!(
                "{coordinator}'s stream root is not an agent.registered event"
            )));
        };
        if existing.display_name != display_name || existing.purpose != purpose {
            return Err(invalid(
                "the agent-registry already has a root epoch and this coordinator's stream \
                 already exists, but with a different display_name/purpose than this genesis \
                 call -- this bus was already activated (possibly differently); use `register` \
                 to add a further agent instead of `genesis`",
            ));
        }
        return Ok((config, epoch, existing_tip));
    }

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
    let commit = crate::stream::create_root_commit(repo, &header, &first_event)?;
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
        assert!(
            err.to_string().contains("unsupported object_format"),
            "{err}"
        );
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
        assert!(
            err.to_string().contains("unsupported merge_engine"),
            "{err}"
        );
    }

    #[test]
    fn parse_rejects_a_product_review_from_of_the_wrong_length_for_its_object_format() {
        // `object_format` can only be "sha1" now (`git2`'s vendored libgit2
        // supports it without an experimental build flag; "sha256" is
        // rejected outright by `parse`'s own format check, exercised
        // separately below) -- so a length mismatch is constructed the other
        // way: a well-formed 64-hex-char id (a valid `ObjectId` on its own,
        // just the wrong length for sha1's 40) paired with `object_format:
        // "sha1"`.
        let sha256_shaped_id = ObjectId::parse("1".repeat(64)).unwrap();
        let value = serde_json::json!({
            "object_format": "sha1",
            "product_review_from": sha256_shaped_id.as_str(),
            "merge_engine": SUPPORTED_MERGE_ENGINE,
            "merge_engine_version": SUPPORTED_MERGE_ENGINE_VERSION,
        });
        let err = BusConfig::parse(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(
            err.to_string().contains("product_review_from length"),
            "{err}"
        );
    }

    #[test]
    fn parse_rejects_sha256_outright() {
        let value = serde_json::json!({
            "object_format": "sha256",
            "product_review_from": "1".repeat(64),
            "merge_engine": SUPPORTED_MERGE_ENGINE,
            "merge_engine_version": SUPPORTED_MERGE_ENGINE_VERSION,
        });
        let err = BusConfig::parse(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(
            err.to_string().contains("unsupported object_format"),
            "{err}"
        );
    }

    #[test]
    fn new_rejects_sha256_outright() {
        let err = BusConfig::new("sha256".to_string(), oid(1)).unwrap_err();
        assert!(
            err.to_string().contains("unsupported object_format"),
            "{err}"
        );
    }

    /// In-process via libgit2 -- see `testfix`'s module doc for why fixtures
    /// stopped spawning `git`.
    fn init_repo() -> tempfile::TempDir {
        crate::testfix::init_repo()
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
        )
        .unwrap();

        assert_eq!(config.object_format, "sha1");
        assert!(epoch.is_active_member(&coord1));
        assert_eq!(
            crate::registry::read_registry_tip(repo.path()).unwrap(),
            Some(epoch.id.clone())
        );
        assert_eq!(
            crate::registry::read_bus_config(repo.path(), &epoch.id).unwrap(),
            config
        );
        assert_eq!(
            crate::stream::read_stream_tip(repo.path(), &coord1).unwrap(),
            Some(first_commit)
        );

        let (header, log) = crate::stream::read_stream(repo.path(), &coord1).unwrap();
        assert_eq!(
            header.registration_authority,
            crate::scalars::EventId::new(&coord1, 0)
        );
        assert_eq!(header.activation_event, None);
        assert_eq!(log.len(), 1);
        assert_eq!(log[0].kind, "agent.registered");
    }

    /// Calling `genesis` again with identical parameters (the "the whole
    /// call completed, but the caller doesn't know that and retries"
    /// case, or simply an idempotent double-invocation) must be a pure
    /// no-op returning the already-created state, not an error.
    #[test]
    fn genesis_is_idempotent_when_called_twice_with_identical_parameters() {
        let repo = init_repo();
        let coord1 = crate::scalars::Agent::parse("coord1".to_string()).unwrap();
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        let call = || {
            genesis(
                repo.path(),
                &coord1,
                crate::scalars::Short::parse("Coordinator One".to_string()).unwrap(),
                crate::scalars::Text::parse("bootstraps the fleet".to_string()).unwrap(),
                "sha1".to_string(),
                ObjectId::parse(review_from.clone()).unwrap(),
                crate::scalars::Short::parse("host1".to_string()).unwrap(),
            )
        };
        let (_config1, epoch1, commit1) = call().unwrap();
        let (_config2, epoch2, commit2) = call().unwrap();
        assert_eq!(epoch1.id, epoch2.id);
        assert_eq!(commit1, commit2);
    }

    /// The actual crash-recovery scenario (section 2.5: "define recovery
    /// for a partially created registry or stream set"): the registry root
    /// commit landed, but a crash happened before the coordinator's own
    /// stream root did. A resumed `genesis` call with the same parameters
    /// must complete the missing half rather than refusing outright with
    /// "already has a root epoch."
    #[test]
    fn genesis_resumes_after_a_crash_between_its_two_commits() {
        let repo = init_repo();
        let coord1 = crate::scalars::Agent::parse("coord1".to_string()).unwrap();
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        let config = BusConfig::new(
            "sha1".to_string(),
            ObjectId::parse(review_from.clone()).unwrap(),
        )
        .unwrap();
        let mut members = std::collections::BTreeMap::new();
        members.insert(
            coord1.clone(),
            crate::registry::MemberBinding {
                role: crate::events::Role::Coordinator,
                host: crate::scalars::Short::parse("host1".to_string()).unwrap(),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        // Simulates the crash: only the registry half of genesis ran.
        crate::registry::create_root(repo.path(), &config, members).unwrap();
        assert_eq!(
            crate::stream::read_stream_tip(repo.path(), &coord1).unwrap(),
            None,
            "the coordinator's stream must not exist yet -- that's the crash this test models"
        );

        let (_config, epoch, commit) = genesis(
            repo.path(),
            &coord1,
            crate::scalars::Short::parse("Coordinator One".to_string()).unwrap(),
            crate::scalars::Text::parse("bootstraps the fleet".to_string()).unwrap(),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            crate::scalars::Short::parse("host1".to_string()).unwrap(),
        )
        .unwrap();
        assert!(epoch.is_active_member(&coord1));
        assert_eq!(
            crate::stream::read_stream_tip(repo.path(), &coord1).unwrap(),
            Some(commit)
        );
    }

    /// The resume check compares the existing root epoch's coordinator
    /// binding field by field, and `host` is one of those fields: a second
    /// `genesis` for the same coordinator from a *different* host is a
    /// different activation claim, not a resume. Every existing resume test
    /// varied the agent, the display name or the purpose, so dropping the
    /// host comparison changed nothing any of them could see.
    #[test]
    fn genesis_refuses_to_resume_from_a_different_host() {
        let repo = init_repo();
        let coord1 = crate::scalars::Agent::parse("coord1".to_string()).unwrap();
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        let call = |host: &str| {
            genesis(
                repo.path(),
                &coord1,
                crate::scalars::Short::parse("Coordinator One".to_string()).unwrap(),
                crate::scalars::Text::parse("bootstraps the fleet".to_string()).unwrap(),
                "sha1".to_string(),
                ObjectId::parse(review_from.clone()).unwrap(),
                crate::scalars::Short::parse(host.to_string()).unwrap(),
            )
        };
        call("host1").unwrap();
        // Same coordinator, same everything else, different host.
        let err = call("host2").unwrap_err();
        assert!(
            err.to_string().contains("does not match this genesis call"),
            "{err}"
        );
        // The original activation is still intact and still resumable.
        call("host1").unwrap();
    }

    /// A resumed call with *different* parameters than the original must
    /// be refused, not silently graft onto someone else's already-
    /// activated bus.
    #[test]
    fn genesis_refuses_to_resume_with_mismatched_parameters() {
        let repo = init_repo();
        let coord1 = crate::scalars::Agent::parse("coord1".to_string()).unwrap();
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        genesis(
            repo.path(),
            &coord1,
            crate::scalars::Short::parse("Coordinator One".to_string()).unwrap(),
            crate::scalars::Text::parse("bootstraps the fleet".to_string()).unwrap(),
            "sha1".to_string(),
            ObjectId::parse(review_from.clone()).unwrap(),
            crate::scalars::Short::parse("host1".to_string()).unwrap(),
        )
        .unwrap();

        // A different coordinator name entirely.
        let err = genesis(
            repo.path(),
            &crate::scalars::Agent::parse("coord2".to_string()).unwrap(),
            crate::scalars::Short::parse("Coordinator Two".to_string()).unwrap(),
            crate::scalars::Text::parse("bootstraps the fleet".to_string()).unwrap(),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            crate::scalars::Short::parse("host1".to_string()).unwrap(),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("does not match this genesis call"),
            "{err}"
        );
    }

    /// Round-2 adversarial review's Significant finding: the resume check
    /// above (same coordinator, same host/role/config) never compared
    /// display_name/purpose against what the coordinator's *own stream*
    /// already recorded -- so once that stream root existed, a second
    /// genesis call for the same coordinator with a different display_name
    /// or purpose would silently succeed and return the old commit,
    /// discarding the caller's new arguments without any error.
    #[test]
    fn genesis_refuses_to_resume_with_a_different_display_name_or_purpose() {
        let repo = init_repo();
        let coord1 = crate::scalars::Agent::parse("coord1".to_string()).unwrap();
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();
        genesis(
            repo.path(),
            &coord1,
            crate::scalars::Short::parse("Coordinator One".to_string()).unwrap(),
            crate::scalars::Text::parse("bootstraps the fleet".to_string()).unwrap(),
            "sha1".to_string(),
            ObjectId::parse(review_from.clone()).unwrap(),
            crate::scalars::Short::parse("host1".to_string()).unwrap(),
        )
        .unwrap();

        let err = genesis(
            repo.path(),
            &coord1,
            crate::scalars::Short::parse("Coordinator One But Different".to_string()).unwrap(),
            crate::scalars::Text::parse("bootstraps the fleet".to_string()).unwrap(),
            "sha1".to_string(),
            ObjectId::parse(review_from.clone()).unwrap(),
            crate::scalars::Short::parse("host1".to_string()).unwrap(),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("different display_name/purpose"),
            "{err}"
        );

        let err = genesis(
            repo.path(),
            &coord1,
            crate::scalars::Short::parse("Coordinator One".to_string()).unwrap(),
            crate::scalars::Text::parse("a whole different purpose".to_string()).unwrap(),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            crate::scalars::Short::parse("host1".to_string()).unwrap(),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("different display_name/purpose"),
            "{err}"
        );
    }
}

#[cfg(test)]
mod pinned_engine_tests {
    use super::*;
    use crate::scalars::ObjectId;

    fn config_pinning(version: &str) -> BusConfig {
        BusConfig {
            object_format: "sha1".to_string(),
            product_review_from: ObjectId::parse("0".repeat(40)).unwrap(),
            merge_engine: SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: version.to_string(),
        }
    }

    fn state_pinning(version: &str) -> crate::state::BusState {
        crate::state::BusState::new(config_pinning(version))
    }

    /// The host actually running the tests is on the pinned version (CI
    /// installs it deliberately), so this is the accepting case.
    #[test]
    fn a_host_on_the_pinned_engine_version_may_construct_candidates() {
        let installed = crate::gitrepo::version().unwrap();
        require_pinned_merge_engine(&state_pinning(&installed)).unwrap();
    }

    /// AGENT_REVIEW.md section 7 names two authorities, and the selected
    /// `merge_engine.activated` epoch is the one that moves. A bus upgrades
    /// its engine by publishing that event; if this check kept reading the
    /// frozen bootstrap value, every host running the newly-selected engine
    /// would be refused, and section 7's own upgrade mechanism would become
    /// the thing that permanently disables merging.
    #[test]
    fn the_selected_engine_epoch_overrides_the_bootstrap_pin_in_both_directions() {
        let installed = crate::gitrepo::version().unwrap();
        let epoch = crate::scalars::EventId::new(
            &crate::scalars::Agent::parse("coord1".to_string()).unwrap(),
            4,
        );
        let short = |v: &str| crate::scalars::Short::parse(v.to_string()).unwrap();

        // Bootstrap pins something nobody runs; the selected epoch pins what
        // this host has. The epoch must win.
        let mut upgraded = state_pinning("0.0.0-stale-bootstrap-pin");
        upgraded.merge_engine_info.insert(
            epoch.clone(),
            (short(SUPPORTED_MERGE_ENGINE), short(&installed)),
        );
        upgraded.current_merge_engine_epoch = Some(epoch.clone());
        require_pinned_merge_engine(&upgraded)
            .expect("the selected epoch must override a stale bootstrap pin");

        // And the other way: bootstrap agrees with this host, but the bus has
        // since selected an engine version this host does not have.
        let mut moved_on = state_pinning(&installed);
        moved_on.merge_engine_info.insert(
            epoch.clone(),
            (short(SUPPORTED_MERGE_ENGINE), short("0.0.0-not-a-real-git")),
        );
        moved_on.current_merge_engine_epoch = Some(epoch);
        let err = require_pinned_merge_engine(&moved_on)
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("0.0.0-not-a-real-git"),
            "the selected epoch must be the authority, got: {err}"
        );
    }

    /// AGENT_REVIEW.md section 12, fixture 13. The version compared against
    /// is the *bus's* pin, not this binary's compile-time constant, so the
    /// fixture pins a version nobody is running rather than mutating the
    /// constant.
    #[test]
    fn a_host_on_a_different_engine_version_is_refused() {
        let err = require_pinned_merge_engine(&state_pinning("0.0.0-not-a-real-git"))
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("0.0.0-not-a-real-git") && err.contains("candidate construction"),
            "the error must name the pin it failed against: {err}"
        );
    }

    #[test]
    fn an_engine_this_helper_cannot_run_is_refused_before_git_is_consulted() {
        let mut config = config_pinning("irrelevant");
        config.merge_engine = "some-other-merge-engine".to_string();
        let err = require_pinned_merge_engine(&crate::state::BusState::new(config))
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("some-other-merge-engine"),
            "expected the engine name to be refused, got: {err}"
        );
    }
}
