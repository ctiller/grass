$ErrorActionPreference = 'Stop'

$repositoryRoot = $PSScriptRoot
$failures = [System.Collections.Generic.List[string]]::new()
$documents = Get-ChildItem -LiteralPath $repositoryRoot -Recurse -File -Filter '*.md' |
    Where-Object {
        $_.FullName -notmatch '[\\/]\.git[\\/]' -and
        $_.FullName -notmatch '[\\/]\.lake[\\/]' -and
        $_.FullName -notmatch '[\\/]\.claude[\\/]'
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
            $relativeDocument = [IO.Path]::GetRelativePath(
                $repositoryRoot, $document.FullName).Replace('\', '/')
            $failures.Add("${relativeDocument}: missing target '${target}'")
        }
    }
}

if ($failures.Count -ne 0) {
    $failures | ForEach-Object { Write-Host $_ -ForegroundColor Red }
    exit 1
}

Write-Host "All relative links in $($documents.Count) Markdown files resolve."
