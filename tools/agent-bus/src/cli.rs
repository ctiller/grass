use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "agent-bus", version, about = "Helper for the Grass agent-bus coordination protocol")]
pub struct Cli {
    /// Path to the product repository (defaults to the current directory's repo).
    #[arg(long, global = true)]
    pub repo: Option<String>,

    #[command(subcommand)]
    pub command: Command,
}

#[derive(Subcommand)]
pub enum Command {
    /// Create the orphan `agent-bus` root commit (one-time repository setup).
    BootstrapInit(BootstrapInitArgs),
    /// Publish this identity's `agent.registered` event (sequence zero).
    Register(RegisterArgs),
    /// Publish an `agent.status` lifecycle update.
    StatusSet(StatusSetArgs),
    /// Publish `agent.resumed`, reactivating this identity under user authority.
    Resume(ResumeArgs),
    /// Publish `agent.retired` (bootstrap coordinators only).
    Retire(RetireArgs),
    /// Publish `schema.activated` (bootstrap coordinators only).
    SchemaActivate(SchemaActivateArgs),
    /// Publish `merge_engine.activated` (bootstrap coordinators only).
    MergeEngineActivate(MergeEngineActivateArgs),
    /// Query lifecycle/scope/plan status for one or all agents.
    Status(StatusArgs),
    /// Replace an implementor's active scope claims.
    #[command(subcommand)]
    Scope(ScopeCmd),
    /// Replace an agent's current plan.
    #[command(subcommand)]
    Plan(PlanCmd),
    /// Publish a `progress.reported` update.
    Progress(ProgressArgs),
    /// Open, acknowledge, resolve, reject, or reassign an issue.
    #[command(subcommand)]
    Issue(IssueCmd),
    /// Request, acknowledge, resolve, reject, or reassign a dependency.
    #[command(subcommand)]
    Dependency(DependencyCmd),
    /// Query dependencies involving one agent.
    Dependencies(DependenciesArgs),
    /// Offer, accept, decline, or withdraw a handoff.
    #[command(subcommand)]
    Handoff(HandoffCmd),
    /// Query open items targeting one agent.
    Inbox(InboxArgs),
    /// Nominate, take, decline, request changes, clear/supersede findings,
    /// reassign, authorize, withdraw, or record a merge/reconcile receipt.
    #[command(subcommand)]
    Review(ReviewCmd),
    /// Construct and tag a deterministic no-conflict merge candidate.
    PrepareMerge(PrepareMergeArgs),
    /// Run the pre-merge gate against a published authorization.
    MergeReady(MergeReadyArgs),
    /// Correlate `main` history with bus authorizations and receipts.
    AuditMain(AuditMainArgs),
    /// Report active scope and unresolved lifecycle conflicts.
    Conflicts(ConflictsArgs),
    /// Resolve a concurrent lifecycle conflict (bootstrap coordinators only).
    #[command(subcommand)]
    Lifecycle(LifecycleCmd),
    /// Print the most recent published events.
    Tail(TailArgs),
    /// Structurally and semantically validate the bus branch.
    Validate(ValidateArgs),
    /// Fetch, rebase, and push one agent's unpublished local commits.
    Sync(SyncArgs),
}

#[derive(Parser)]
pub struct BootstrapInitArgs {
    #[arg(long)]
    pub coordinator: Vec<String>,
    #[arg(long)]
    pub product_review_from: String,
}

#[derive(Parser)]
pub struct RegisterArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub display_name: String,
    #[arg(long)]
    pub role: String,
    #[arg(long)]
    pub purpose: String,
    #[arg(long)]
    pub product_base: Option<String>,
    #[arg(long)]
    pub product_branch: Option<String>,
    #[arg(long)]
    pub provider: Option<String>,
    #[arg(long)]
    pub model: Option<String>,
}

#[derive(Parser)]
pub struct StatusSetArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub status: String,
    #[arg(long, default_value = "")]
    pub note: String,
    #[arg(long)]
    pub product_branch: Option<String>,
    #[arg(long)]
    pub product_commit: Option<String>,
}

#[derive(Parser)]
pub struct ResumeArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub reason: String,
    #[arg(long)]
    pub user_authority: String,
}

#[derive(Parser)]
pub struct RetireArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub target: String,
    #[arg(long)]
    pub reason: String,
    #[arg(long)]
    pub user_authority: String,
}

#[derive(Parser)]
pub struct SchemaActivateArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub version: u32,
    #[arg(long)]
    pub design_commit: String,
    #[arg(long)]
    pub helper_commit: String,
}

#[derive(Parser)]
pub struct MergeEngineActivateArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub previous_epoch: String,
    #[arg(long)]
    pub merge_engine: String,
    #[arg(long)]
    pub merge_engine_version: String,
    #[arg(long)]
    pub design_commit: String,
    #[arg(long)]
    pub helper_commit: String,
}

#[derive(Parser)]
pub struct StatusArgs {
    #[arg(long)]
    pub agent: Option<String>,
    #[arg(long)]
    pub json: bool,
}

#[derive(Subcommand)]
pub enum ScopeCmd {
    Set(FileAgentArgs),
}

#[derive(Subcommand)]
pub enum PlanCmd {
    Set(FileAgentArgs),
}

#[derive(Parser)]
pub struct ProgressArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub file: String,
}

#[derive(Parser)]
pub struct FileAgentArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub file: String,
}

#[derive(Subcommand)]
pub enum IssueCmd {
    Open {
        #[arg(long)]
        agent: String,
        #[arg(long)]
        to: String,
        #[arg(long)]
        file: String,
    },
    Acknowledge {
        #[arg(long)]
        agent: String,
        issue_id: String,
        #[arg(long, default_value = "")]
        note: String,
    },
    Resolve {
        #[arg(long)]
        agent: String,
        issue_id: String,
        #[arg(long)]
        file: String,
    },
    Reject {
        #[arg(long)]
        agent: String,
        issue_id: String,
        #[arg(long)]
        file: String,
    },
    Reassign {
        #[arg(long)]
        agent: String,
        issue_id: String,
        #[arg(long)]
        new_target: String,
        #[arg(long)]
        reason: String,
    },
}

#[derive(Subcommand)]
pub enum DependencyCmd {
    Request {
        #[arg(long)]
        agent: String,
        #[arg(long)]
        to: String,
        #[arg(long)]
        file: String,
    },
    Acknowledge {
        #[arg(long)]
        agent: String,
        dependency_id: String,
        #[arg(long, default_value = "")]
        note: String,
    },
    Resolve {
        #[arg(long)]
        agent: String,
        dependency_id: String,
        #[arg(long)]
        file: String,
    },
    Reject {
        #[arg(long)]
        agent: String,
        dependency_id: String,
        #[arg(long)]
        reason: String,
    },
    Reassign {
        #[arg(long)]
        agent: String,
        dependency_id: String,
        #[arg(long)]
        new_target: String,
        #[arg(long)]
        reason: String,
    },
}

#[derive(Parser)]
pub struct DependenciesArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub json: bool,
}

#[derive(Subcommand)]
pub enum HandoffCmd {
    Offer {
        #[arg(long)]
        agent: String,
        #[arg(long)]
        file: String,
    },
    Accept {
        #[arg(long)]
        agent: String,
        handoff_id: String,
        #[arg(long, default_value = "")]
        note: String,
    },
    Decline {
        #[arg(long)]
        agent: String,
        handoff_id: String,
        #[arg(long)]
        reason: String,
    },
    Withdraw {
        #[arg(long)]
        agent: String,
        handoff_id: String,
        #[arg(long)]
        reason: String,
    },
}

#[derive(Parser)]
pub struct InboxArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub json: bool,
}

#[derive(Subcommand)]
pub enum ReviewCmd {
    Nominate {
        #[arg(long)]
        agent: String,
        #[arg(long)]
        file: String,
    },
    Take {
        #[arg(long)]
        agent: String,
        nomination: String,
        #[arg(long, default_value = "")]
        note: String,
    },
    Decline {
        #[arg(long)]
        agent: String,
        nomination: String,
        #[arg(long)]
        reason: String,
    },
    Changes {
        #[arg(long)]
        agent: String,
        #[arg(long)]
        file: String,
    },
    Clear {
        #[arg(long)]
        agent: String,
        #[arg(long)]
        file: String,
    },
    Supersede {
        #[arg(long)]
        agent: String,
        #[arg(long)]
        file: String,
    },
    Reassign {
        #[arg(long)]
        agent: String,
        #[arg(long)]
        file: String,
    },
    Authorize {
        #[arg(long)]
        agent: String,
        #[arg(long)]
        file: String,
    },
    Withdraw {
        #[arg(long)]
        agent: String,
        nomination: String,
        #[arg(long)]
        reason: String,
    },
    Merged {
        #[arg(long)]
        agent: String,
        #[arg(long)]
        file: String,
    },
    Reconcile {
        #[arg(long)]
        agent: String,
        #[arg(long)]
        file: String,
    },
}

#[derive(Parser)]
pub struct PrepareMergeArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub nomination: String,
    #[arg(long)]
    pub reviewed_commit: String,
}

#[derive(Parser)]
pub struct MergeReadyArgs {
    #[arg(long)]
    pub agent: String,
    #[arg(long)]
    pub authorization: String,
    #[arg(long)]
    pub json: bool,
}

#[derive(Parser)]
pub struct AuditMainArgs {
    #[arg(long)]
    pub to: Option<String>,
    #[arg(long)]
    pub json: bool,
}

#[derive(Parser)]
pub struct ConflictsArgs {
    #[arg(long)]
    pub json: bool,
}

#[derive(Subcommand)]
pub enum LifecycleCmd {
    Resolve(FileAgentArgs),
}

#[derive(Parser)]
pub struct TailArgs {
    #[arg(long)]
    pub agent: Option<String>,
    #[arg(long, default_value_t = 20)]
    pub count: usize,
    #[arg(long)]
    pub json: bool,
}

#[derive(Parser)]
pub struct ValidateArgs {
    #[arg(long)]
    pub incremental: Option<String>,
    #[arg(long)]
    pub linked: bool,
    #[arg(long)]
    pub quarantine_invalid: bool,
    #[arg(long)]
    pub json: bool,
}

#[derive(Parser)]
pub struct SyncArgs {
    #[arg(long)]
    pub agent: String,
}
