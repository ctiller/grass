#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd "$repo_root"
probe_directory=.lake/grass-windows-probes
mkdir -p -- "$probe_directory"
phase=arguments
# A failed invocation must never leave a previous successful manifest current.
printf '%s\n' '{"status":"incomplete","passed":false}' > "$probe_directory/result.json"
printf '%s\n' '{"status":"not-started","passed":false}' > "$probe_directory/native-result.json"
finish_probe() {
  local exit_code=$?
  if ((exit_code != 0)); then
    printf '{"status":"failed","phase":"%s","exitCode":%d,"passed":false}\n' \
      "$phase" "$exit_code" > "$probe_directory/result.json"
  fi
}
trap finish_probe EXIT
emit_only=false
case "${1-}" in
  '') ;;
  --emit-only) emit_only=true ;;
  *) printf 'Usage: %s [--emit-only]\n' "$0" >&2; exit 2 ;;
esac
if (($# > 1)); then printf 'Unexpected extra arguments.\n' >&2; exit 2; fi

phase=build
lake_exe=$(command -v lake || command -v lake.exe) || { printf 'lake is required.\n' >&2; exit 1; }
"$lake_exe" build Tests.Platform.Win32LoaderEntry
# The exporter reads source bytes at runtime, avoiding cached include_source_chars.
# The captured source snapshot and expected static payload accompany the image.
phase=emission
"$lake_exe" env lean --run Tools/EmitGrassHello.lean \
  "$probe_directory/hello.exe" "$probe_directory/expected-stdout.bin" "$probe_directory/source.lean"
if "$emit_only"; then
  printf '%s\n' '{"status":"emitted-only","nativeExecuted":false,"passed":false}' > "$probe_directory/result.json"
  printf 'Grass PE and exact input snapshot emitted in %s. No native execution requested.\n' "$probe_directory"
  exit 0
fi

case "$(uname -s)" in
  MINGW*|MSYS*|CYGWIN*) ;;
  *) printf 'Native launch requires Windows; use --emit-only on this host.\n' >&2; exit 77 ;;
esac
phase=native
pwsh_exe=$(command -v pwsh || command -v pwsh.exe) || { printf 'PowerShell 7 is required for Windows process capture.\n' >&2; exit 1; }
"$pwsh_exe" -NoLogo -NoProfile -File probes/windows/capture-grass-hello.ps1 \
  -ImagePath "$probe_directory/hello.exe" \
  -ExpectedPath "$probe_directory/expected-stdout.bin" \
  -SourceSnapshotPath "$probe_directory/source.lean" \
  -ResultPath "$probe_directory/native-result.json"
cp -- "$probe_directory/native-result.json" "$probe_directory/result.json"
