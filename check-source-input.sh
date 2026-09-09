#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$repo_root"
lake_exe=$(command -v lake || command -v lake.exe) || { echo 'lake is required by check-source-input.sh' >&2; exit 1; }
lake() { "$lake_exe" "$@"; }

# include_source_chars embeds authored files during elaboration, outside Lake's
# import dependency graph. Build imports, then force every embedding fixture
# through Lean. Discover the population instead of maintaining a second list.
# Text mentions may conservatively include a helper or comment-only module;
# those extra elaborations are harmless and do not narrow freshness coverage.
lake build Tests

inventory=$(mktemp)
trap 'rm -f -- "$inventory"' EXIT
# Check the producer directly: process substitution would hide find's status.
find Tests -type f -name '*.lean' -print0 > "$inventory"
fixtures=()
while IFS= read -r -d '' fixture; do
  if grep -Fq 'include_source_chars' "$fixture"; then
    fixtures+=("$fixture")
  else
    status=$?
    if (( status != 1 )); then
      printf 'Could not inspect source fixture %s\n' "$fixture" >&2
      exit "$status"
    fi
  fi
done < "$inventory"
if (( ${#fixtures[@]} == 0 )); then
  echo 'No authored-source embedding fixtures found.' >&2
  exit 1
fi
for fixture in "${fixtures[@]}"; do
  lake env lean "$fixture"
done
printf 'Re-elaborated %d source-embedding modules.\n' "${#fixtures[@]}"
