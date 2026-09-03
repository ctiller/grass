mod apply;
mod bootstrap;
mod canon;
mod cli;
mod common;
mod coordinator;
mod envelope;
mod error;
mod events;
mod exclusive;
mod frontier;
mod gitrepo;
mod merge_candidate;
mod merge_ready;
mod outbox;
mod publish;
mod registry;
mod scalars;
mod state;
mod storage;
mod stream;
mod sync;

fn main() {
    use clap::Parser;
    let cli = cli::Cli::parse();
    if let Err(e) = cli::run(cli) {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}
