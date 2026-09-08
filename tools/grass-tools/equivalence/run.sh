#!/usr/bin/env bash
# Drives the equivalence comparison for one group of tools.
#
#   run.sh assemblers <corpus-dir> <binary-dir>   # nasm, ndisasm, decode
#   run.sh probe      <corpus-dir> <binary-dir>   # machine probe
#
# The split is not cosmetic. `x86-machine-probe` executes the bytes under test
# on the processor, which it does by mapping an executable page with
# `VirtualAlloc` and catching hardware faults with a vectored exception handler
# -- Windows-only in both implementations. Run on Linux, every probe reports
# `faulted 0x00000001` from a worker that could not start, in both, so the two
# would agree while measuring nothing. The probe group therefore runs on a
# Windows runner, where the campaign is real.
#
# Exit status is 1 if any case differed, and names the cases.
set -uo pipefail

GROUP="${1:?usage: run.sh <assemblers|probe> <corpus-dir> <binary-dir>}"
CORPORA="${2:?corpus directory}"
BIN="${3:?binary directory}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../../.." && pwd)"

: "${PYTHON:=python3}"
export PYTHON
export WORK="${WORK:-${RUNNER_TEMP:-/tmp}/x86-equivalence}"
export FAILURES="$WORK/failures"
rm -rf "$WORK"; mkdir -p "$WORK"; : > "$FAILURES"

FAULTS="$WORK/faults"
bash "$HERE/faults.sh" "$CORPORA" "$FAULTS"
echo
# shellcheck source=compare.sh
. "$HERE/compare.sh"

# On Windows the built binaries carry a .exe suffix.
suffix=""
[ -x "$BIN/x86-nasm-differential.exe" ] && suffix=".exe"
py() { printf '%s/Tools/%s.py' "$REPO" "$1"; }
rs() { printf '%s/%s%s' "$BIN" "$1" "$suffix"; }

if [ "$GROUP" = assemblers ]; then
  echo "### x86-nasm-differential ###"
  compare "nasm/real-corpus"              "$(py x86-nasm-differential)" "$(rs x86-nasm-differential)" "$CORPORA/corpus.txt"
  compare "nasm/injected-encoding-defect" "$(py x86-nasm-differential)" "$(rs x86-nasm-differential)" "$FAULTS/corpus.badbytes.txt"
  compare "nasm/shrunk-corpus"            "$(py x86-nasm-differential)" "$(rs x86-nasm-differential)" "$FAULTS/corpus.short.txt"
  compare "nasm/tampered-coverage"        "$(py x86-nasm-differential)" "$(rs x86-nasm-differential)" "$FAULTS/corpus.baddigest.txt"
  compare "nasm/empty-corpus"             "$(py x86-nasm-differential)" "$(rs x86-nasm-differential)" "$FAULTS/corpus.empty.txt"

  echo "### x86-ndisasm-differential ###"
  compare "ndisasm/real-corpus"              "$(py x86-ndisasm-differential)" "$(rs x86-ndisasm-differential)" "$CORPORA/rip.txt"
  compare "ndisasm/injected-encoding-defect" "$(py x86-ndisasm-differential)" "$(rs x86-ndisasm-differential)" "$FAULTS/rip.badbytes.txt"
  compare "ndisasm/malformed-row"            "$(py x86-ndisasm-differential)" "$(rs x86-ndisasm-differential)" "$FAULTS/rip.malformed.txt"
  compare "ndisasm/shrunk-corpus"            "$(py x86-ndisasm-differential)" "$(rs x86-ndisasm-differential)" "$FAULTS/rip.short.txt"
  compare "ndisasm/tampered-coverage"        "$(py x86-ndisasm-differential)" "$(rs x86-ndisasm-differential)" "$FAULTS/rip.baddigest.txt"

  echo "### x86-decode-differential ###"
  compare "decode/real-corpus"           "$(py x86-decode-differential)" "$(rs x86-decode-differential)" "$CORPORA/decode.txt"
  compare "decode/injected-length-defect" "$(py x86-decode-differential)" "$(rs x86-decode-differential)" "$FAULTS/decode.badlen.txt"
  compare "decode/wrong-window-size"     "$(py x86-decode-differential)" "$(rs x86-decode-differential)" "$FAULTS/decode.badwindow.txt"
  compare "decode/shrunk-corpus"         "$(py x86-decode-differential)" "$(rs x86-decode-differential)" "$FAULTS/decode.short.txt"
  compare "decode/tampered-coverage"     "$(py x86-decode-differential)" "$(rs x86-decode-differential)" "$FAULTS/decode.baddigest.txt"
elif [ "$GROUP" = probe ]; then
  echo "### x86-machine-probe ###"
  compare "probe/real-corpus"          "$(py x86-machine-probe)" "$(rs x86-machine-probe)" "$CORPORA/probes.txt"
  compare "probe/injected-model-defect" "$(py x86-machine-probe)" "$(rs x86-machine-probe)" "$FAULTS/probes.badafter.txt"
  compare "probe/shrunk-corpus"        "$(py x86-machine-probe)" "$(rs x86-machine-probe)" "$FAULTS/probes.short.txt"
  compare "probe/tampered-coverage"    "$(py x86-machine-probe)" "$(rs x86-machine-probe)" "$FAULTS/probes.baddigest.txt"
  compare "probe/malformed-row"        "$(py x86-machine-probe)" "$(rs x86-machine-probe)" "$FAULTS/probes.malformed.txt"
else
  echo "::error::unknown group '$GROUP'; expected 'assemblers' or 'probe'"
  exit 2
fi

# The oracle-absent case, last, and separately: it is the one that says the
# comparison is not passing vacuously.
#
# `Tools/win64-unwind-differential.py` was found to report a clean run when its
# assembler was missing, so "both refused" has to be shown rather than assumed
# here. Each of these four tools searches PATH and then two or three fixed
# Windows install directories, so PATH alone is not enough to hide the oracle:
# the home directory both fall back through is pointed at an empty directory
# too. What must come out is a loud refusal from both, with the same words and
# the same non-zero status -- not a clean report over zero comparisons.
echo "### the oracle absent from both ###"
NOWHERE="$WORK/nowhere"; mkdir -p "$NOWHERE"
(
  cd "$NOWHERE" || exit 1
  export HOME="$NOWHERE" USERPROFILE="$NOWHERE"
  export PATH="/usr/bin:/bin:/usr/local/bin"
  for tool in nasm ndisasm; do
    if command -v "$tool" >/dev/null 2>&1; then
      echo "::error::$tool is still reachable here, so this case proves nothing"
      exit 1
    fi
  done
  if [ "$GROUP" = assemblers ]; then
    compare "nasm/oracle-absent"    "$(py x86-nasm-differential)"    "$(rs x86-nasm-differential)"    "$CORPORA/corpus.txt"
    compare "ndisasm/oracle-absent" "$(py x86-ndisasm-differential)" "$(rs x86-ndisasm-differential)" "$CORPORA/rip.txt"
    compare "decode/oracle-absent"  "$(py x86-decode-differential)"  "$(rs x86-decode-differential)"  "$CORPORA/decode.txt"
  else
    compare "probe/oracle-absent"   "$(py x86-machine-probe)"        "$(rs x86-machine-probe)"        "$CORPORA/probes.txt"
  fi
)

# Every oracle-absent case must have exited non-zero in *both* implementations.
# `compare` only checks that the two agree, and two implementations that both
# reported a clean run over a missing oracle would agree perfectly.
echo "### the oracle-absent cases refused rather than passed ###"
absent_ok=0
for d in "$WORK"/*oracle-absent*; do
  [ -d "$d" ] || continue
  if grep -q 'not found on PATH' "$d/py.err" && grep -q 'not found on PATH' "$d/rs.err"; then
    echo "  $(basename "$d"): both refused, naming the missing oracle"
    absent_ok=$((absent_ok + 1))
  else
    echo "::error::$(basename "$d") did not refuse when its oracle was absent"
    echo "oracle-absent/$(basename "$d")" >> "$FAILURES"
  fi
done
if [ "$absent_ok" = 0 ]; then
  echo "::error::no oracle-absent case ran, so the vacuous-pass check proves nothing"
  exit 1
fi
echo

if [ -s "$FAILURES" ]; then
  echo "::error::the port is not equivalent to the original on these cases:"
  sed 's/^/  /' "$FAILURES"
  exit 1
fi
echo "every case agreed: same stdout, same stderr, same exit status."
