$ErrorActionPreference = 'Stop'

$repositoryRoot = $PSScriptRoot

function Get-PathUnder([string] $Base, [string] $Full) {
    # [IO.Path]::GetRelativePath is .NET Core / .NET 5+ only. It was previously
    # called only in the failure path, so on Windows PowerShell 5.1 this script
    # crashed precisely when it had a broken link to report.
    $normalizedBase = [IO.Path]::GetFullPath($Base).TrimEnd('\', '/')
    $normalizedFull = [IO.Path]::GetFullPath($Full)
    $separator = [IO.Path]::DirectorySeparatorChar
    if (-not $normalizedFull.StartsWith($normalizedBase + $separator, [StringComparison]::Ordinal)) {
        throw "$normalizedFull is not underneath $normalizedBase"
    }
    return $normalizedFull.Substring($normalizedBase.Length + 1).Replace('\', '/')
}

$failures = [System.Collections.Generic.List[string]]::new()
# The exclusions are matched against the path *relative to the repository root*,
# never against the absolute path. Every agent works in a Claude Code worktree at
# <repo>/.claude/worktrees/<name>, so matching '.claude' against the absolute path
# excluded the repository root itself and therefore every file beneath it: the
# script reported success over zero documents and exited 0. A gate that fails open
# is worse than no gate, and this one is a required_check on review nominations.
$documents = Get-ChildItem -LiteralPath $repositoryRoot -Recurse -File -Filter '*.md' |
    Where-Object {
        $relative = Get-PathUnder $repositoryRoot $_.FullName
        $relative -notmatch '^\.git/' -and
        $relative -notmatch '^\.lake/' -and
        $relative -notmatch '^\.claude/' -and
        $relative -notmatch '/\.git/' -and
        $relative -notmatch '/\.lake/' -and
        $relative -notmatch '/\.claude/'
    }

foreach ($document in $documents) {
    $text = Get-Content -LiteralPath $document.FullName -Raw -Encoding utf8
    $links = [regex]::Matches($text, '!?(?:\[[^\]]*\])\((?<target>[^)]+)\)')

    foreach ($link in $links) {
        $target = $link.Groups['target'].Value.Trim()
        if ($target.StartsWith('<') -and $target.EndsWith('>')) {
            $target = $target.Substring(1, $target.Length - 2)
        }

        $path = ($target -split '#', 2)[0]
        if ([string]::IsNullOrWhiteSpace($path) -or
            $path -match '^[a-zA-Z][a-zA-Z0-9+.-]*:') {
            continue
        }

        $decodedPath = [uri]::UnescapeDataString($path)
        $resolvedPath = Join-Path $document.DirectoryName $decodedPath
        if (-not (Test-Path -LiteralPath $resolvedPath)) {
            $relativeDocument = Get-PathUnder $repositoryRoot $document.FullName
            $failures.Add("${relativeDocument}: missing target '${target}'")
        }
    }
}

if ($failures.Count -ne 0) {
    $failures | ForEach-Object { Write-Host $_ -ForegroundColor Red }
    exit 1
}

Write-Host "All relative links in $($documents.Count) Markdown files resolve."
