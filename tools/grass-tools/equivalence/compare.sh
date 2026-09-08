#!/usr/bin/env bash
# Byte-comparison harness for the x86 tool port.
#
# Four Python entry points under `Tools/` are being replaced by binaries in this
# crate. `docs/VALIDATION.md` section 2 calls a tool a fallible oracle, and that
# applies to a *port* as much as to NASM: the only thing that makes the new
# binary trustworthy is that it says the same thing as the implementation whose
# reviews the surrounding documentation cites. So this runs both over identical
# argv and compares stdout, stderr and the exit status byte for byte.
#
# Why it lives in CI rather than in a unit test. Three of these four tools do
# their real work by invoking NASM or NDISASM, and the fourth executes bytes on
# the processor. A unit test can exercise the parsing and the reporting around
# that -- and the ports carry 91 of them -- but not the interaction with the
# tool itself. A previous attempt at this port stopped for exactly that reason:
# with no assembler installed, the only comparable path was the one where the
# oracle is missing and both implementations refuse, which is not equivalence
# evidence. Installing NASM on the runner is what makes the comparison real.
#
# Why it also runs over injected faults. A comparison that only ever sees two
# clean runs agree has not been shown to be able to disagree. `faults.sh` builds
# corpora carrying one named defect each -- a corrupted encoding, a wrong
# decoded length, a wrong predicted register file, a shrunk corpus, a tampered
# coverage column -- so every case below is one where both implementations must
# produce a specific *complaint*, and the harness compares the complaints.
#
# Usage:
#   . compare.sh                       # provides `compare`
#   compare <label> <python> <binary> [args...]
#
# Environment:
#   PYTHON    the interpreter to run the original with
#   WORK      a scratch directory for captured streams and diffs
#   FAILURES  a file that accumulates the label of every differing case
set -uo pipefail

: "${PYTHON:?compare.sh needs PYTHON}"
: "${WORK:?compare.sh needs WORK}"
: "${FAILURES:?compare.sh needs FAILURES}"

# The declared differences, and only these.
#
# 1. Line endings. Python's `sys.stdout`/`sys.stderr` are text streams with
#    `newline=None`, so on Windows every "\n" it writes becomes "\r\n"; Rust
#    writes the byte it was given. That is a property of the interpreter, not of
#    either tool, and it would otherwise make every line of every stream differ
#    on the Windows job. Both sides are folded to LF.
#
# 2. How each implementation names itself when it tells the reader what to run.
#    The Python messages say `x86-nasm-differential.py`, and the decode tool's
#    usage text says `python Tools/x86-decode-differential.py decode.txt`. The
#    ports say the binary name instead, deliberately: a message telling the
#    reader to run a file that is no longer the tool sends them looking for the
#    wrong thing. Rewriting the Python side to the binary name compares the
#    sentence rather than the invocation.
#
# 3. The line of `x86-machine-probe`'s host block that records what ran. Python
#    prints `python:    3.12.10`; the port prints
#    `harness:   x86-machine-probe <version> (rust)`. It is not a translation
#    of the same fact -- claiming a Python version from a Rust binary would be a
#    fiction in a record whose entire purpose is to say what was run -- so there
#    is nothing to compare and the line is replaced on both sides.
#
# Every substitution is counted and printed, so a reader can see that rule 2 and
# rule 3 fire on the lines they are meant to and nowhere else.
normalise() {
  tr -d '\r' | sed -E \
    -e 's#python3? Tools/(x86-[a-z0-9-]+)\.py#\1#g' \
    -e 's#(x86-[a-z0-9-]+)\.py#\1#g' \
    -e 's#^  (python:|harness:) +.*$#  <harness identification>#'
}

compare() {
  local label="$1"; shift
  local py="$1"; shift
  local rs="$1"; shift

  local slug
  slug="$(printf '%s' "$label" | tr -c 'A-Za-z0-9' '-')"
  local d="$WORK/$slug"
  mkdir -p "$d"

  "$PYTHON" "$py" "$@" > "$d/py.out.raw" 2> "$d/py.err.raw"
  local pyrc=$?
  "$rs" "$@" > "$d/rs.out.raw" 2> "$d/rs.err.raw"
  local rsrc=$?

  local f
  for f in py.out py.err rs.out rs.err; do
    normalise < "$d/$f.raw" > "$d/$f"
  done

  echo "=================================================================="
  echo "CASE  $label"
  echo "  python  exit $pyrc   stdout $(wc -c < "$d/py.out.raw") B   stderr $(wc -c < "$d/py.err.raw") B"
  echo "  rust    exit $rsrc   stdout $(wc -c < "$d/rs.out.raw") B   stderr $(wc -c < "$d/rs.err.raw") B"

  # Show what normalisation touched, so it cannot quietly absorb a real
  # difference. Line endings are folded before this comparison, so only rules 2
  # and 3 can appear here.
  local touched=0
  for f in py.out py.err rs.out rs.err; do
    local before after
    before="$(tr -d '\r' < "$d/$f.raw")"
    after="$(cat "$d/$f")"
    if [ "$before" != "$after" ]; then
      diff <(printf '%s\n' "$before") <(printf '%s\n' "$after") \
        | sed -n "s|^< |    normalised out of $f: |p"
      touched=1
    fi
  done
  [ "$touched" = 0 ] && echo "  (no declared difference was normalised in this case)"

  local bad=0
  if [ "$pyrc" != "$rsrc" ]; then
    echo "  DIFFERENCE: exit status -- python $pyrc, rust $rsrc"
    bad=1
  fi
  for f in out err; do
    if ! diff -u --label "python ($f)" --label "rust ($f)" \
          "$d/py.$f" "$d/rs.$f" > "$d/$f.diff"; then
      echo "  DIFFERENCE: $f"
      sed 's/^/    /' "$d/$f.diff"
      bad=1
    fi
  done

  if [ "$bad" = 0 ]; then
    echo "  IDENTICAL   exit $pyrc, $(wc -l < "$d/py.out") stdout line(s), $(wc -l < "$d/py.err") stderr line(s)"
    # Print what they agreed on. A case whose agreed output is a bare
    # "no disagreement" and one whose agreed output names a caught defect are
    # very different evidence, and the log has to let a reader tell them apart.
    sed 's/^/    | /' "$d/py.out" "$d/py.err" 2>/dev/null | head -25
  else
    echo "$label" >> "$FAILURES"
  fi
  echo
}
