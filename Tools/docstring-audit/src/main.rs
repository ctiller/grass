use rayon::prelude::*;
use regex::Regex;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

const CLAIM_WORDS: &[&str] = &[
    "ensures",
    "ensuring",
    "prevents",
    "preventing",
    "cannot",
    "preserves",
    "guarantees",
    "makes it impossible",
    "is enforced",
    "only if",
    "only when",
];

const HEDGES: &[&str] = &[
    "intended",
    "not enforced",
    "cannot be made",
    "owes",
    "owed",
    "open obligation",
    "used to",
    "an earlier",
    "m2",
    "m3",
    "m4",
    "m5",
    "m6",
    "m7",
    "m8",
    "m9",
    "m10",
    "no arrangement",
    "is not the check",
    "not by itself",
    "on its own",
    "nothing here",
    "cannot tell",
    "is not that",
    "not something",
    "no way to",
    "unrepresentable",
    "cannot state",
    "cannot be demonstrated",
    "cannot read",
    "cannot fault",
    "cannot lawfully",
    "cannot coexist",
    "cannot be checked",
    "cannot introduce",
    "cannot enforce",
    "cannot answer",
    "cannot express",
    "cannot know",
    "cannot be erased or masked",
];

struct Auditor {
    known: HashSet<String>,
    hedge_re: Regex,
    lean_style_name: Regex,
    ident_re: Regex,
    not_ident_re: Regex,
    doc_block_re: Regex,
}

fn split_sentences(text: &str) -> Vec<&str> {
    let mut sentences = Vec::new();
    let mut start = 0;
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'.' {
            let next = i + 1;
            if next == bytes.len() || bytes[next].is_ascii_whitespace() {
                let s = &text[start..=i];
                if !s.trim().is_empty() {
                    sentences.push(s.trim());
                }
                let mut j = next;
                while j < bytes.len() && bytes[j].is_ascii_whitespace() {
                    j += 1;
                }
                start = j;
                i = j;
                continue;
            }
        }
        i += 1;
    }
    if start < text.len() {
        let s = &text[start..];
        if !s.trim().is_empty() {
            sentences.push(s.trim());
        }
    }
    sentences
}

impl Auditor {
    fn new(known: HashSet<String>) -> Self {
        let hedge_patterns: Vec<String> = HEDGES
            .iter()
            .map(|h| format!(r"\b{}\b", regex::escape(h)))
            .collect();
        let hedge_regex_str = hedge_patterns.join("|");
        let hedge_re = Regex::new(&format!("(?i){}", hedge_regex_str)).unwrap();

        let lean_style_name =
            Regex::new(r"^[a-z][A-Za-z0-9']*(_[A-Za-z0-9'][A-Za-z0-9']*)+$").unwrap();
        let ident_re = Regex::new(r"`([A-Za-z_][A-Za-z0-9_.?!']*)`").unwrap();
        let not_ident_re = Regex::new(r"^(docs/|§|[a-z]+\s)").unwrap();
        let doc_block_re = Regex::new(r"(?s)/-[-!](.*?)-/").unwrap();

        Self {
            known,
            hedge_re,
            lean_style_name,
            ident_re,
            not_ident_re,
            doc_block_re,
        }
    }

    fn check_file(&self, path: &Path) -> Vec<String> {
        let source = match fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Warning: could not read {}: {}", path.display(), e);
                return Vec::new();
            }
        };

        let posix_path = path.to_string_lossy().replace('\\', "/");
        let mut findings = Vec::new();

        for cap in self.doc_block_re.captures_iter(&source) {
            let m = cap.get(0).unwrap();
            let block = cap.get(1).unwrap().as_str();
            let line = source[..m.start()].matches('\n').count() + 1;

            // Flatten block to single-space separated lines
            let flattened: String = block
                .lines()
                .map(|l| l.trim())
                .filter(|l| !l.is_empty())
                .collect::<Vec<_>>()
                .join(" ");

            for sentence in split_sentences(&flattened) {
                let s = sentence.trim();
                if s.is_empty() {
                    continue;
                }

                let lowered = s.to_lowercase();
                if !CLAIM_WORDS.iter().any(|&w| lowered.contains(w)) {
                    continue;
                }

                if self.hedge_re.is_match(&lowered) {
                    continue;
                }

                if s.contains("docs/") && s.contains('"') {
                    continue;
                }

                let mut named: Vec<String> = Vec::new();
                for id_cap in self.ident_re.captures_iter(s) {
                    let ident = id_cap.get(1).unwrap().as_str();
                    if !self.not_ident_re.is_match(ident) {
                        named.push(ident.to_string());
                    }
                }

                let resolved: Vec<&String> = named.iter().filter(|id| self.known.contains(id.as_str())).collect();
                let invented: Vec<&String> = named
                    .iter()
                    .filter(|id| !self.known.contains(id.as_str()) && self.lean_style_name.is_match(id))
                    .collect();

                if !invented.is_empty() {
                    let invented_strs: Vec<String> = invented.into_iter().map(|s| format!("'{}'", s)).collect();
                    findings.push(format!(
                        "{}:{}: claim names [{}], which look like declarations and are not in the build: {:?}",
                        posix_path, line, invented_strs.join(", "), s
                    ));
                } else if !named.is_empty() && resolved.is_empty() {
                    let named_strs: Vec<String> = named.into_iter().map(|s| format!("'{}'", s)).collect();
                    findings.push(format!(
                        "{}:{}: claim names [{}] but the build knows no such declaration: {:?}",
                        posix_path, line, named_strs.join(", "), s
                    ));
                } else if named.is_empty() {
                    findings.push(format!(
                        "{}:{}: claim names no enforcing type or theorem: {:?}",
                        posix_path, line, s
                    ));
                }
            }
        }

        findings
    }
}

fn newest_olean_mtime(dir: &Path) -> Option<std::time::SystemTime> {
    let mut newest = None;
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                if let Some(t) = newest_olean_mtime(&path) {
                    newest = Some(newest.map_or(t, |n: std::time::SystemTime| n.max(t)));
                }
            } else if path.extension().and_then(|e| e.to_str()) == Some("olean") {
                if let Ok(meta) = entry.metadata() {
                    if let Ok(t) = meta.modified() {
                        newest = Some(newest.map_or(t, |n: std::time::SystemTime| n.max(t)));
                    }
                }
            }
        }
    }
    newest
}

fn load_declarations() -> HashSet<String> {
    let cache_path = PathBuf::from(".lake/build/declnames.txt");
    let exe_name = if cfg!(windows) { "declnames.exe" } else { "declnames" };
    let exe_path = PathBuf::from(".lake/build/bin").join(exe_name);

    let cache_valid = if cache_path.is_file() && exe_path.is_file() {
        if let (Ok(c_meta), Ok(e_meta)) = (cache_path.metadata(), exe_path.metadata()) {
            let c_time = c_meta.modified().unwrap_or(std::time::SystemTime::UNIX_EPOCH);
            let e_time = e_meta.modified().unwrap_or(std::time::SystemTime::UNIX_EPOCH);
            let lean_lib = PathBuf::from(".lake/build/lib/lean/Grass");
            let olean_time = newest_olean_mtime(&lean_lib).unwrap_or(std::time::SystemTime::UNIX_EPOCH);
            c_time >= e_time && c_time >= olean_time
        } else {
            false
        }
    } else {
        false
    };

    let content = if cache_valid {
        fs::read_to_string(&cache_path).unwrap_or_default()
    } else {
        if !exe_path.is_file() {
            println!("declnames executable not found; building with `lake build declnames`...");
            let status = Command::new("lake")
                .args(["build", "declnames"])
                .status()
                .expect("failed to run `lake build declnames`");
            if !status.success() {
                eprintln!("could not build declnames executable");
                std::process::exit(1);
            }
        }

        let output = Command::new(&exe_path)
            .output()
            .expect("failed to execute declnames binary");

        if !output.status.success() {
            eprintln!(
                "could not obtain declaration list from {}: {}",
                exe_path.display(),
                String::from_utf8_lossy(&output.stderr)
            );
            std::process::exit(1);
        }

        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let _ = fs::write(&cache_path, &stdout);
        stdout
    };

    let mut known = HashSet::new();

    for line in content.lines() {
        let name = line.trim();
        if name.is_empty() || name.contains(' ') {
            continue;
        }
        let parts: Vec<&str> = name.split('.').collect();
        for i in 0..parts.len() {
            known.insert(parts[i..].join("."));
        }
    }

    known.insert("Prop".to_string());
    known.insert("Type".to_string());
    known.insert("Sort".to_string());

    if known.len() < 1000 {
        eprintln!(
            "declaration list has only {} entries, which cannot be right; refusing to report clean audit",
            known.len()
        );
        std::process::exit(1);
    }

    known
}

fn collect_lean_files(dir: &Path, files: &mut Vec<PathBuf>) {
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                collect_lean_files(&path, files);
            } else if path.extension().map_or(false, |ext| ext == "lean") {
                files.push(path);
            }
        }
    }
}

fn main() -> ExitCode {
    let known = load_declarations();
    let auditor = Auditor::new(known);

    let mut files = Vec::new();
    let root = Path::new("Grass");
    if root.is_dir() {
        collect_lean_files(root, &mut files);
    }
    files.sort();

    let findings: Vec<String> = files
        .par_iter()
        .flat_map(|path| auditor.check_file(path))
        .collect();

    if !findings.is_empty() {
        println!("docstring audit: claims that name nothing enforcing them\n");
        for f in &findings {
            println!("  {}", f);
        }
        println!(
            "\n{} unbacked claim(s). Name the type or theorem, or rewrite as an intended invariant or open obligation.",
            findings.len()
        );
        ExitCode::FAILURE
    } else {
        println!("docstring audit: every strong claim names an enforcing type or theorem");
        ExitCode::SUCCESS
    }
}
