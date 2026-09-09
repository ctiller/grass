#!/usr/bin/env bash
# Build the Windows adapter from Git Bash with the installed MSVC x64 tools.
set -euo pipefail
case "$(uname -s)" in
  MINGW*|MSYS*|CYGWIN*) ;;
  *) echo 'The Windows worker requires Git Bash on Windows and MSVC x64 tools.' >&2; exit 1 ;;
esac
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
command -v cygpath >/dev/null || { echo 'cygpath is required' >&2; exit 1; }
vswhere=${VSWHERE:-'/c/Program Files (x86)/Microsoft Visual Studio/Installer/vswhere.exe'}
[[ -x "$vswhere" ]] || { echo 'Visual Studio Installer/vswhere.exe is required (or set VSWHERE).' >&2; exit 1; }
installation=$("$vswhere" -latest -products '*' -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath | tr -d '\r')
[[ -n "$installation" ]] || { echo 'MSVC x64 tools are required' >&2; exit 1; }
vcvars="$installation\\VC\\Auxiliary\\Build\\vcvars64.bat"
[[ -f "$(cygpath -u "$vcvars")" ]] || { echo 'vcvars64.bat not found' >&2; exit 1; }
out=${1:-"$script_dir/../../target/x86-native"}
[[ $# -le 1 ]] || { echo 'usage: build.sh [output-directory]' >&2; exit 1; }
mkdir -p -- "$out"
out=$(cygpath -aw "$out")
source_file=$(cygpath -aw "$script_dir/windows.c")
# These characters are expanded even inside quoted batch paths. Reject them
# rather than let a directory name become cmd.exe syntax.
for path in "$out" "$source_file" "$vcvars"; do
  case "$path" in *'%'*|*'!'*|*'"'*|*$'\r'*|*$'\n'*)
    echo 'Build paths cannot contain percent, exclamation, quote or newline characters.' >&2; exit 1 ;;
  esac
done
batch=$(cygpath -u "$out")/build.cmd
printf '%s\r\n' \
  '@echo off' \
  "call \"$vcvars\" >nul" \
  'if errorlevel 1 exit /b 1' \
  "cl /nologo /W4 /WX /O2 /Fe:\"$out\\windows.exe\" /Fo:\"$out\\windows.obj\" \"$source_file\" /link /INCREMENTAL:NO" > "$batch"
# Disable MSYS argument rewriting: /c and MSVC switches are native arguments.
MSYS_NO_PATHCONV=1 cmd.exe /d /c "$(cygpath -w "$batch")"
