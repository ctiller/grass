param(
    [ValidateRange(1, 5)]
    [int[]] $Spike = @(1, 2, 3, 4, 5)
)

$ErrorActionPreference = 'Stop'

$pairs = @(
    @{ Number = 1; Directory = '1_Hello_World' },
    @{ Number = 2; Directory = '2_Sort' },
    @{ Number = 3; Directory = '3_Gzip' },
    @{ Number = 4; Directory = '4_Web_Server' },
    @{ Number = 5; Directory = '5_Spinning_Cube' }
) | Where-Object { $Spike -contains $_.Number }

function ConvertTo-NormalizedSource([string] $Text) {
    return $Text.Replace("`r`n", "`n").Replace("`r", "`n").TrimEnd("`n")
}

$failed = $false

foreach ($pair in $pairs) {
    $documentPath = Join-Path $PSScriptRoot "docs/SPIKE_$($pair.Number).md"
    $sourceDirectory = Join-Path $PSScriptRoot "Spikes/$($pair.Directory)"
    $document = Get-Content -LiteralPath $documentPath -Raw -Encoding utf8
    $heading = '## Exact authored source snapshot'
    $headingIndex = $document.LastIndexOf($heading, [StringComparison]::Ordinal)

    if ($headingIndex -lt 0) {
        Write-Host "SPIKE_$($pair.Number): no exact authored source snapshot" -ForegroundColor Red
        $failed = $true
        continue
    }

    $snapshot = $document.Substring($headingIndex)
    $pattern = '(?ms)^### `(?<name>[^`]+\.lean)`\r?\n\r?\n```lean\r?\n(?<source>.*?)\r?\n```'
    $documentSources = [System.Collections.Generic.Dictionary[string,string]]::new(
        [StringComparer]::Ordinal)

    foreach ($match in [regex]::Matches($snapshot, $pattern)) {
        $name = $match.Groups['name'].Value.Replace('\', '/')
        if ($documentSources.ContainsKey($name)) {
            Write-Host "SPIKE_$($pair.Number): duplicate snapshot path $name" -ForegroundColor Red
            $failed = $true
            continue
        }
        $documentSources.Add(
            $name,
            (ConvertTo-NormalizedSource $match.Groups['source'].Value))
    }

    $directoryFiles = @(Get-ChildItem -LiteralPath $sourceDirectory -Filter '*.lean' -Recurse |
        Sort-Object FullName)
    $directoryPaths = @($directoryFiles | ForEach-Object {
        [IO.Path]::GetRelativePath($sourceDirectory, $_.FullName).Replace('\', '/')
    } | Sort-Object -CaseSensitive)
    $documentPaths = @($documentSources.Keys | Sort-Object -CaseSensitive)

    if ([string]::Join("`n", $directoryPaths) -cne [string]::Join("`n", $documentPaths)) {
        Write-Host "SPIKE_$($pair.Number): authored file manifest differs" -ForegroundColor Red
        Compare-Object $directoryPaths $documentPaths -CaseSensitive | Format-Table
        $failed = $true
    }

    foreach ($file in $directoryFiles) {
        $relativePath = [IO.Path]::GetRelativePath(
            $sourceDirectory, $file.FullName).Replace('\', '/')
        if (-not $documentSources.ContainsKey($relativePath)) {
            continue
        }

        $actual = ConvertTo-NormalizedSource (
            Get-Content -LiteralPath $file.FullName -Raw -Encoding utf8)
        if ($actual -cne $documentSources[$relativePath]) {
            Write-Host "SPIKE_$($pair.Number): $relativePath differs from its document snapshot" -ForegroundColor Red
            $failed = $true
        }
    }
}

if ($failed) {
    exit 1
}

Write-Host 'All selected spike authored source snapshots match their directories under the documented normalization.'
