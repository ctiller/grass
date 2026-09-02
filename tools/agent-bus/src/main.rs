mod apply;
mod bootstrap;
mod bus;
mod canon;
mod cli;
mod commands;
mod common;
mod envelope;
mod error;
mod events;
mod gitrepo;
mod history;
mod lock;
mod review_cmds;
mod scalars;
mod state;
mod storage;
#[cfg(test)]
mod test_support;
mod validate_cmd;

use clap::Parser;
use cli::{Command, DependencyCmd, HandoffCmd, IssueCmd, LifecycleCmd, PlanCmd, ReviewCmd, ScopeCmd};
use scalars::{Agent, ObjectId};

fn main() {
    let cli = cli::Cli::parse();
    if let Err(e) = run(cli) {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}

fn run(cli: cli::Cli) -> error::AbResult<()> {
    if let Command::BootstrapInit(args) = &cli.command {
        let ctx = bus::BusCtx::discover(cli.repo.as_deref())?;
        let coordinators: Vec<Agent> = args
            .coordinator
            .iter()
            .map(|s| Agent::parse(s.clone()))
            .collect::<error::AbResult<_>>()?;
        let review_from = ObjectId::parse(args.product_review_from.clone())?;
        bus::bootstrap_init(&ctx, &coordinators, &review_from)?;
        println!("bootstrapped agent-bus with coordinators: {:?}", args.coordinator);
        return Ok(());
    }

    let ctx = bus::BusCtx::discover(cli.repo.as_deref())?;
    match &cli.command {
        Command::BootstrapInit(_) => unreachable!(),
        Command::Register(a) => commands::register(&ctx, a),
        Command::StatusSet(a) => commands::status_set(&ctx, a),
        Command::Resume(a) => commands::resume(&ctx, a),
        Command::Retire(a) => commands::retire(&ctx, a),
        Command::SchemaActivate(a) => commands::schema_activate(&ctx, a),
        Command::MergeEngineActivate(a) => commands::merge_engine_activate(&ctx, a),
        Command::Status(a) => commands::status(&ctx, a),
        Command::Scope(ScopeCmd::Set(a)) => commands::scope_set(&ctx, a),
        Command::Plan(PlanCmd::Set(a)) => commands::plan_set(&ctx, a),
        Command::Progress(a) => commands::progress(&ctx, a),
        Command::Issue(cmd) => match cmd {
            IssueCmd::Open { agent, to, file } => commands::issue_open(&ctx, agent, to, file),
            IssueCmd::Acknowledge { agent, issue_id, note } => commands::issue_acknowledge(&ctx, agent, issue_id, note),
            IssueCmd::Resolve { agent, issue_id, file } => commands::issue_resolve(&ctx, agent, issue_id, file),
            IssueCmd::Reject { agent, issue_id, file } => commands::issue_reject(&ctx, agent, issue_id, file),
            IssueCmd::Reassign { agent, issue_id, new_target, reason } => {
                commands::issue_reassign(&ctx, agent, issue_id, new_target, reason)
            }
        },
        Command::Dependency(cmd) => match cmd {
            DependencyCmd::Request { agent, to, file } => commands::dependency_request(&ctx, agent, to, file),
            DependencyCmd::Acknowledge { agent, dependency_id, note } => {
                commands::dependency_acknowledge(&ctx, agent, dependency_id, note)
            }
            DependencyCmd::Resolve { agent, dependency_id, file } => {
                commands::dependency_resolve(&ctx, agent, dependency_id, file)
            }
            DependencyCmd::Reject { agent, dependency_id, reason } => {
                commands::dependency_reject(&ctx, agent, dependency_id, reason)
            }
            DependencyCmd::Reassign { agent, dependency_id, new_target, reason } => {
                commands::dependency_reassign(&ctx, agent, dependency_id, new_target, reason)
            }
        },
        Command::Dependencies(a) => commands::dependencies(&ctx, a),
        Command::Handoff(cmd) => match cmd {
            HandoffCmd::Offer { agent, file } => commands::handoff_offer(&ctx, agent, file),
            HandoffCmd::Accept { agent, handoff_id, note } => commands::handoff_accept(&ctx, agent, handoff_id, note),
            HandoffCmd::Decline { agent, handoff_id, reason } => {
                commands::handoff_decline(&ctx, agent, handoff_id, reason)
            }
            HandoffCmd::Withdraw { agent, handoff_id, reason } => {
                commands::handoff_withdraw(&ctx, agent, handoff_id, reason)
            }
        },
        Command::Inbox(a) => commands::inbox(&ctx, a),
        Command::Review(cmd) => match cmd {
            ReviewCmd::Nominate { agent, file } => review_cmds::nominate(&ctx, agent, file),
            ReviewCmd::Take { agent, nomination, note } => review_cmds::take(&ctx, agent, nomination, note),
            ReviewCmd::Decline { agent, nomination, reason } => review_cmds::decline(&ctx, agent, nomination, reason),
            ReviewCmd::Changes { agent, file } => review_cmds::changes(&ctx, agent, file),
            ReviewCmd::Clear { agent, file } => review_cmds::clear(&ctx, agent, file),
            ReviewCmd::Supersede { agent, file } => review_cmds::supersede(&ctx, agent, file),
            ReviewCmd::Reassign { agent, file } => review_cmds::reassign(&ctx, agent, file),
            ReviewCmd::Authorize { agent, file } => review_cmds::authorize(&ctx, agent, file),
            ReviewCmd::Withdraw { agent, nomination, reason } => review_cmds::withdraw(&ctx, agent, nomination, reason),
            ReviewCmd::Merged { agent, file } => review_cmds::merged(&ctx, agent, file),
            ReviewCmd::Reconcile { agent, file } => review_cmds::reconcile(&ctx, agent, file),
        },
        Command::PrepareMerge(a) => review_cmds::prepare_merge(&ctx, &a.agent, &a.nomination, &a.reviewed_commit),
        Command::MergeReady(a) => review_cmds::merge_ready(&ctx, &a.agent, &a.authorization, a.json),
        Command::AuditMain(a) => review_cmds::audit_main(&ctx, a.to.as_deref(), a.json),
        Command::Conflicts(a) => commands::conflicts(&ctx, a),
        Command::Lifecycle(LifecycleCmd::Resolve(a)) => commands::lifecycle_resolve(&ctx, a),
        Command::Tail(a) => commands::tail(&ctx, a),
        Command::Validate(a) => {
            validate_cmd::validate(&ctx, a.incremental.as_deref(), a.linked, a.quarantine_invalid, a.json)
        }
        Command::Sync(a) => commands::sync(&ctx, a),
    }
}
