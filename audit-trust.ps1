[CmdletBinding()]
param(
    [string[]]$LibrarySourceRoot = @("Grass"),
    [string[]]$TestSourceRoot = @("Tests"),
    [string[]]$Declaration = @(
        "Grass.StableId.render_of_empty_namespace",
        "Grass.RequirementKind.extension_injective",
        "Grass.DemandCertificateFamily.get",
        "Grass.ObservationProjection.identity_project",
        "Grass.ObservationProjection.comp_project",
        "Grass.RelationalSystem.Steps.graphExtends",
        "Grass.RelationalSystem.Runs.graphExtends",
        "Grass.BehaviorRefinement.mapSteps",
        "Grass.BehaviorRefinement.mapInfinite",
        "Grass.BehaviorRefinement.mapCompletion",
        "Grass.BehaviorRefinement.mapRuns",
        "Grass.BehaviorRefinement.preservesAcceptance",
        "Grass.VerifiedProgram.loadedBehavior_exact",
        "Grass.VerifiedProgram.sound",
        "Grass.VerifiedProgram.execution_nonempty",
        "Grass.emitProgram_parses"
    ),
    [string[]]$AllowedAxiom = @(
        "propext",
        "Classical.choice",
        "Quot.sound"
    )
)

$ErrorActionPreference = "Stop"

if ($Declaration.Count -eq 0) {
    throw "At least one declaration must be audited."
}

$moduleNames = @()
foreach ($root in $LibrarySourceRoot) {
    if (-not (Test-Path -LiteralPath $root -PathType Container)) {
        throw "Configured library source root '$root' does not exist."
    }
    foreach ($file in Get-ChildItem -LiteralPath $root -Filter '*.lean' -File -Recurse) {
        $relative = [System.IO.Path]::GetRelativePath((Get-Location).Path, $file.FullName)
        $withoutExtension = $relative.Substring(0, $relative.Length - '.lean'.Length)
        $moduleNames += $withoutExtension.Replace([System.IO.Path]::DirectorySeparatorChar, '.')
    }
}
foreach ($root in $TestSourceRoot) {
    if (-not (Test-Path -LiteralPath $root -PathType Container)) {
        throw "Configured test source root '$root' does not exist."
    }
    foreach ($file in Get-ChildItem -LiteralPath $root -Filter '*.lean' -File -Recurse) {
        $relative = [System.IO.Path]::GetRelativePath((Get-Location).Path, $file.FullName)
        $withoutExtension = $relative.Substring(0, $relative.Length - '.lean'.Length)
        $moduleNames += $withoutExtension.Replace([System.IO.Path]::DirectorySeparatorChar, '.')
    }
}
$moduleNames = @($moduleNames | Sort-Object -Unique)

$temporaryPath = [System.IO.Path]::Combine(
    [System.IO.Path]::GetTempPath(),
    "grass-axiom-audit-$([System.Guid]::NewGuid().ToString('N')).lean"
)

try {
    $commands = @($moduleNames | ForEach-Object { "import $_" })
    $commands += "#audit_verified_programs"
    $commands += $Declaration | ForEach-Object { "#print axioms $_" }
    [System.IO.File]::WriteAllLines($temporaryPath, $commands)

    $output = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -ne 0) {
        $output | ForEach-Object { Write-Error $_ }
        throw "Lean could not audit the requested declaration closure."
    }

    $reported = 0
    foreach ($line in $output) {
        if ($line -match "^'[^']+' does not depend on any axioms$") {
            $reported += 1
            continue
        }

        if ($line -match "^'[^']+' depends on axioms: \[(.*)\]$") {
            $reported += 1
            $used = @($Matches[1].Split(',') | ForEach-Object { $_.Trim() })
            $rejected = @($used | Where-Object { $_ -notin $AllowedAxiom })
            if ($rejected.Count -ne 0) {
                throw "Rejected transitive axiom(s): $($rejected -join ', ')"
            }
            continue
        }

        Write-Host $line
    }

    if ($reported -ne $Declaration.Count) {
        throw "Expected $($Declaration.Count) axiom reports, received $reported."
    }

    $negativeProbe = @(
        "import Tests.Foundation",
        "open Grass",
        "@[irreducible] def HiddenVerifiedProgram : Type 1 := VerifiedProgram Grass.Tests.Foundation.spec",
        "axiom hiddenVerifiedProgram : HiddenVerifiedProgram",
        "#audit_verified_programs"
    )
    [System.IO.File]::WriteAllLines($temporaryPath, $negativeProbe)
    $negativeOutput = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -eq 0 -or
        -not ($negativeOutput -match "hiddenVerifiedProgram.*rejected axioms")) {
        $negativeOutput | ForEach-Object { Write-Host $_ }
        throw "Trust audit did not reject a producer behind an irreducible result alias."
    }

    Write-Host "Trust audit passed for $reported declaration(s)."
}
finally {
    if ([System.IO.File]::Exists($temporaryPath)) {
        [System.IO.File]::Delete($temporaryPath)
    }
}
