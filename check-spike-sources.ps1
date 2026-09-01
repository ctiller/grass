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
    $document = ConvertTo-NormalizedSource (
        Get-Content -LiteralPath $documentPath -Raw -Encoding utf8)
    $lines = $document -split "`n"
    $documentSources = [System.Collections.Generic.Dictionary[string,string]]::new(
        [StringComparer]::Ordinal)
    $identities = [System.Collections.Generic.HashSet[string]]::new(
        [StringComparer]::Ordinal)
    $blockCount = 0

    for ($index = 0; $index -lt $lines.Count; $index++) {
        if ($lines[$index] -notmatch '^```') {
            continue
        }

        $blockCount++
        if ($index -eq 0 -or
            $lines[$index - 1] -notmatch '^<!-- grass-block: (?<body>.+) -->$') {
            Write-Host "SPIKE_$($pair.Number): block $blockCount has no immediate classification" -ForegroundColor Red
            $failed = $true
            $classification = $null
        } else {
            $classification = $Matches['body']
        }

        $closing = $index + 1
        while ($closing -lt $lines.Count -and $lines[$closing] -notmatch '^```$') {
            $closing++
        }
        if ($closing -ge $lines.Count) {
            Write-Host "SPIKE_$($pair.Number): block $blockCount is unterminated" -ForegroundColor Red
            $failed = $true
            break
        }

        $content = if ($closing -eq $index + 1) {
            ''
        } else {
            [string]::Join("`n", $lines[($index + 1)..($closing - 1)])
        }

        if ($null -ne $classification) {
            $identity = $null
            if ($classification -match '^authored file=(?<path>[^ ]+)$') {
                $path = $Matches['path'].Replace('\', '/')
                $identity = "authored:$path"
                if ($lines[$index] -ne '```lean') {
                    Write-Host "SPIKE_$($pair.Number): authored $path is not a Lean block" -ForegroundColor Red
                    $failed = $true
                }
                if ($documentSources.ContainsKey($path)) {
                    Write-Host "SPIKE_$($pair.Number): duplicate authored path $path" -ForegroundColor Red
                    $failed = $true
                } else {
                    $documentSources.Add($path, (ConvertTo-NormalizedSource $content))
                }
            } elseif ($classification -match '^generated id=(?<id>[^ ]+) derives=(?<derives>.+)$') {
                $identity = "generated:$($Matches['id'])"
                if ([string]::IsNullOrWhiteSpace($Matches['derives'])) {
                    Write-Host "SPIKE_$($pair.Number): generated block lacks derives authority" -ForegroundColor Red
                    $failed = $true
                }
            } elseif ($classification -match '^(?<kind>interface|proof-sketch) id=(?<id>[^ ]+)$') {
                $identity = "$($Matches['kind']):$($Matches['id'])"
            } else {
                Write-Host "SPIKE_$($pair.Number): invalid classification '$classification'" -ForegroundColor Red
                $failed = $true
            }

            if ($null -ne $identity -and -not $identities.Add($identity)) {
                Write-Host "SPIKE_$($pair.Number): duplicate block identity $identity" -ForegroundColor Red
                $failed = $true
            }
        }

        $index = $closing
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
            Write-Host "SPIKE_$($pair.Number): $relativePath differs from its authored block" -ForegroundColor Red
            $failed = $true
        }
    }
}

if ($failed) {
    exit 1
}

Write-Host 'All selected spike blocks are classified, uniquely identified, and exact authored sources match their directories.'
