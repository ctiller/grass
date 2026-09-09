//! The bus-wide configuration fixed at version-two activation
//! (docs/AGENT_COORDINATION_EVOLUTION.md section 2.5): the product object
//! format, the exact product commit migration started from, and the merge
//! engine metadata. Unlike version one's single immutable `_bus/BUS.json`, this
//! is not a standalone commit of its own -- it's established alongside the
//! registry's root epoch (`registry.rs`), since activation and the first
//! roster epoch are one atomic act. There is deliberately no `coordinators`
//! list here: coordinator authority is `Role::Coordinator` membership in the
//! registry's current epoch, not a separate immutable roster.

use crate::error::{invalid, AbResult};
use crate::scalars::ObjectId;
use serde::{Deserialize, Serialize};

pub const SUPPORTED_MERGE_ENGINE: &str = "git-ort";

/// What newly activated buses record in [`BusConfig::merge_engine_version`].
///
/// There is deliberately no version here to compare against. The repository
/// owner rejected treating a particular `git` build as protocol authority
/// (g-design:249): agents need only ordinary `git pull`/`fetch` and non-force
/// push, so no host may be refused for the version it happens to run, and no
/// immutable history may be made sensitive to a reader's build constant.
///
/// The field itself survives because buses activated before that ruling
/// recorded a real version in it, and their `_bus/BUS.json` must keep
/// parsing. It is an ignored diagnostic in both directions: nothing reads an
/// old bus's value to decide anything, and nothing compares this one.
pub const UNPINNED_MERGE_ENGINE_VERSION: &str = "unpinned";

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct BusConfig {
    pub object_format: String,
    pub product_review_from: ObjectId,
    pub merge_engine: String,
    /// Diagnostic only, and never compared with anything. Buses activated
    /// before g-design:249 recorded a specific `git` version here and must
    /// keep parsing; new ones record [`UNPINNED_MERGE_ENGINE_VERSION`]. See
    /// that constant, and `genesis`'s resume check, which deliberately
    /// ignores this field.
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
        // Activation neither runs nor inspects this host's `git`. It does not
        // read `git --version` at all, which is the point: a bus is a thing
        // agents read, publish to and sync -- none of that is engine work,
        // and making activation depend on a subprocess gave a host with a
        // merely *unusual* git (or a malformed `~/.gitconfig`, which makes
        // `git --version` exit nonzero with empty stdout) no way to start or
        // open a bus at all.
        //
        // `merge_engine_version` is therefore recorded, not decided: see
        // `UNPINNED_MERGE_ENGINE_VERSION`.
        Ok(BusConfig {
            object_format,
            product_review_from,
            merge_engine: SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: UNPINNED_MERGE_ENGINE_VERSION.to_string(),
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
/// exact call (same load-bearing config, same sole coordinator member)
/// before treating it as a resume point -- a genuinely different prior
/// activation, or one that has already moved past its root epoch, is refused
/// rather than silently adopted. If the coordinator's own stream root is
/// also already there, this is a pure idempotent no-op returning the
/// existing commit.
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
            // Only the load-bearing half of the config decides whether this
            // is the same activation. `merge_engine`/`merge_engine_version`
            // are diagnostics (see `UNPINNED_MERGE_ENGINE_VERSION`), and a
            // bus activated before g-design:249 records a real git version
            // in the latter -- comparing it would make resuming, or
            // idempotently re-running, `genesis` against an existing bus
            // fail on every host and every build but the one that first ran
            // it, which is the same reader-build sensitivity that ruling
            // removed everywhere else.
            let same_activation = existing_config.object_format == config.object_format
                && existing_config.product_review_from == config.product_review_from;
            if existing.parent.is_some() || !same_activation || !sole_coordinator {
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

    /// The exact version buses activated before g-design:249 recorded in
    /// `merge_engine_version`. Real fleet history contains it, so `parse`
    /// must go on accepting it -- as an ignored diagnostic, not as something
    /// to agree or disagree with.
    const HISTORICAL_PINNED_VERSION: &str = "2.53.0";

    #[test]
    fn to_canonical_bytes_round_trips_through_parse() {
        let config = BusConfig {
            object_format: "sha1".to_string(),
            product_review_from: oid(1),
            merge_engine: SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: HISTORICAL_PINNED_VERSION.to_string(),
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
            "merge_engine_version": HISTORICAL_PINNED_VERSION,
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
            "merge_engine_version": HISTORICAL_PINNED_VERSION,
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
            "merge_engine_version": HISTORICAL_PINNED_VERSION,
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
            "merge_engine_version": HISTORICAL_PINNED_VERSION,
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

    pub(super) fn init_repo() -> tempfile::TempDir {
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

/// The engine pin is gone, and these are the properties that replaced it
/// (g-design:249).
///
/// They are stated as their own module because the deleted
/// `pinned_engine_tests` stated the opposite ones, and the pair should be
/// read together in `git log`: every test here fails if a
/// `require_pinned_merge_engine`, or anything shaped like it, comes back.
#[cfg(test)]
mod unpinned_engine_tests {
    use super::tests::init_repo;
    use super::*;
    use crate::scalars::ObjectId;

    fn coord() -> crate::scalars::Agent {
        crate::scalars::Agent::parse("coord1".to_string()).unwrap()
    }

    fn short(s: &str) -> crate::scalars::Short {
        crate::scalars::Short::parse(s.to_string()).unwrap()
    }

    fn text(s: &str) -> crate::scalars::Text {
        crate::scalars::Text::parse(s.to_string()).unwrap()
    }

    fn sole_coordinator(
        agent: &crate::scalars::Agent,
    ) -> std::collections::BTreeMap<crate::scalars::Agent, crate::registry::MemberBinding> {
        let mut members = std::collections::BTreeMap::new();
        members.insert(
            agent.clone(),
            crate::registry::MemberBinding {
                role: crate::events::Role::Coordinator,
                host: short("host1"),
                coordinator_custody_epoch: 0,
                standby: None,
            },
        );
        members
    }

    /// Activation records a version nobody compares against, and reads
    /// nothing about this host to decide it.
    #[test]
    fn activation_records_an_unpinned_engine_version() {
        let config = BusConfig::new("sha1".to_string(), ObjectId::parse("0".repeat(40)).unwrap())
            .expect("activation must not depend on which git this host runs");
        assert_eq!(config.merge_engine_version, UNPINNED_MERGE_ENGINE_VERSION);
        assert_eq!(
            config.merge_engine_version, "unpinned",
            "the recorded value must not be readable as a version at all -- a real-looking \
             version invites a future reader to compare it with something"
        );
    }

    /// A `_bus/BUS.json` written before the ruling records a real git
    /// version. It must still parse, and round-trip, unchanged.
    #[test]
    fn a_config_recording_a_historical_pinned_version_still_parses() {
        let value = serde_json::json!({
            "object_format": "sha1",
            "product_review_from": "0".repeat(40),
            "merge_engine": SUPPORTED_MERGE_ENGINE,
            "merge_engine_version": "2.53.0",
        });
        let parsed = BusConfig::parse(&serde_json::to_vec(&value).unwrap()).unwrap();
        assert_eq!(parsed.merge_engine_version, "2.53.0");
        assert_eq!(
            BusConfig::parse(&parsed.to_canonical_bytes()).unwrap(),
            parsed
        );
    }

    /// A version this crate has never heard of parses too. "Historical" is
    /// not a whitelist of values some build once pinned.
    #[test]
    fn a_config_recording_an_unknown_engine_version_still_parses() {
        let value = serde_json::json!({
            "object_format": "sha1",
            "product_review_from": "0".repeat(40),
            "merge_engine": SUPPORTED_MERGE_ENGINE,
            "merge_engine_version": "9.99.0-nobody-ships-this",
        });
        let parsed = BusConfig::parse(&serde_json::to_vec(&value).unwrap()).unwrap();
        assert_eq!(parsed.merge_engine_version, "9.99.0-nobody-ships-this");
    }

    /// The mixed-version half of activation: a bus whose registry root was
    /// written by an *older build* -- one that recorded `2.53.0` -- must
    /// still be resumable, and idempotently re-runnable, by this build.
    ///
    /// `genesis` used to compare the whole `BusConfig` for equality, which
    /// meant the recorded engine version decided whether a second `genesis`
    /// call was "the same activation". Once this build stopped recording
    /// `2.53.0`, every real bus in the fleet would have answered "no": the
    /// crash-recovery path (section 2.5) and plain idempotent re-runs would
    /// both have failed with "already activated (possibly differently)",
    /// which is exactly the reader-build sensitivity the ruling removes.
    #[test]
    fn genesis_resumes_a_bus_whose_root_recorded_a_different_engine_version() {
        let repo = init_repo();
        let coord1 = coord();
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();

        // The registry half, as an older build would have written it.
        let older_build_config = BusConfig {
            object_format: "sha1".to_string(),
            product_review_from: ObjectId::parse(review_from.clone()).unwrap(),
            merge_engine: SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: "2.53.0".to_string(),
        };
        assert_ne!(
            older_build_config.merge_engine_version, UNPINNED_MERGE_ENGINE_VERSION,
            "the fixture must actually differ from what this build records, or it proves nothing"
        );
        crate::registry::create_root(repo.path(), &older_build_config, sole_coordinator(&coord1))
            .unwrap();

        let (config, epoch, commit) = genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps the fleet"),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            short("host1"),
        )
        .expect("a bus recording another build's engine version must still be resumable");
        assert!(epoch.is_active_member(&coord1));
        assert_eq!(
            crate::stream::read_stream_tip(repo.path(), &coord1).unwrap(),
            Some(commit)
        );
        // The bus's own recorded config is untouched by the resume; only the
        // value this call would have written differs.
        assert_eq!(config.merge_engine_version, UNPINNED_MERGE_ENGINE_VERSION);
        assert_eq!(
            crate::registry::read_bus_config(repo.path(), &epoch.id)
                .unwrap()
                .merge_engine_version,
            "2.53.0",
            "resuming must not rewrite the immutable root the older build published"
        );
    }

    /// The load-bearing half of the config is still compared. Relaxing the
    /// engine fields must not have relaxed `product_review_from`, which
    /// genuinely does say which bus this is.
    #[test]
    fn genesis_still_refuses_a_root_naming_a_different_product_review_from() {
        let repo = init_repo();
        let coord1 = coord();
        let review_from = crate::gitrepo::rev_parse(repo.path(), "HEAD").unwrap();

        let other = BusConfig {
            object_format: "sha1".to_string(),
            product_review_from: ObjectId::parse("1".repeat(40)).unwrap(),
            merge_engine: SUPPORTED_MERGE_ENGINE.to_string(),
            merge_engine_version: UNPINNED_MERGE_ENGINE_VERSION.to_string(),
        };
        crate::registry::create_root(repo.path(), &other, sole_coordinator(&coord1)).unwrap();

        let err = genesis(
            repo.path(),
            &coord1,
            short("Coordinator One"),
            text("bootstraps the fleet"),
            "sha1".to_string(),
            ObjectId::parse(review_from).unwrap(),
            short("host1"),
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("does not match this genesis call"),
            "{err}"
        );
    }
}
