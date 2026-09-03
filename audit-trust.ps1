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
        "Grass.VerifiedProgram.execution_completes",
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
$externalProbeModule = "AuditExternalProbe$([System.Guid]::NewGuid().ToString('N'))"
$externalProbePath = Join-Path (Get-Location).Path "$externalProbeModule.lean"
$externalProbeOlean = Join-Path (Get-Location).Path ".lake/build/lib/lean/$externalProbeModule.olean"
$runtimeProbeModule = "AuditRuntimeProbe$([System.Guid]::NewGuid().ToString('N'))"
$runtimeProbePath = Join-Path (Get-Location).Path "$runtimeProbeModule.lean"
$runtimeProbeOlean = Join-Path (Get-Location).Path ".lake/build/lib/lean/$runtimeProbeModule.olean"
$csimpProbeModule = "AuditScopedCSimpProbe$([System.Guid]::NewGuid().ToString('N'))"
$csimpProbePath = Join-Path (Get-Location).Path "$csimpProbeModule.lean"
$csimpProbeOlean = Join-Path (Get-Location).Path ".lake/build/lib/lean/$csimpProbeModule.olean"
$runtimeConsumerModule = "AuditRuntimeConsumer$([System.Guid]::NewGuid().ToString('N'))"
$runtimeConsumerPath = Join-Path (Get-Location).Path "$runtimeConsumerModule.lean"
$runtimeConsumerOlean = Join-Path (Get-Location).Path ".lake/build/lib/lean/$runtimeConsumerModule.olean"

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

    $irreducibleDiscoveryProbe = @(
        "import Tests.Foundation",
        "open Grass",
        "@[irreducible] def HiddenVerifiedProgram : Type 1 := VerifiedProgram Grass.Tests.Foundation.spec",
        "def cleanHiddenVerifiedProgram : HiddenVerifiedProgram := by",
        "  unfold HiddenVerifiedProgram",
        "  exact Grass.Tests.Foundation.verified",
        "#audit_verified_programs"
    )
    [System.IO.File]::WriteAllLines($temporaryPath, $irreducibleDiscoveryProbe)
    $irreducibleDiscoveryOutput = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -ne 0 -or
        -not ($irreducibleDiscoveryOutput -match "cleanHiddenVerifiedProgram")) {
        $irreducibleDiscoveryOutput | ForEach-Object { Write-Host $_ }
        throw "Trust audit did not discover a producer behind an irreducible result alias."
    }

    $wrappedNegativeProbe = @(
        "import Tests.Foundation",
        "open Grass",
        "namespace AuditProbe",
        "axiom boxedVerifiedProgram : Nonempty (VerifiedProgram Grass.Tests.Foundation.spec)",
        "noncomputable def emittedBytes : ByteArray := emitProgram (Classical.choice boxedVerifiedProgram)",
        "end AuditProbe",
        "#audit_verified_programs"
    )
    [System.IO.File]::WriteAllLines($temporaryPath, $wrappedNegativeProbe)
    $wrappedNegativeOutput = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -eq 0 -or
        -not ($wrappedNegativeOutput -match "emittedBytes.*boxedVerifiedProgram")) {
        $wrappedNegativeOutput | ForEach-Object { Write-Host $_ }
        throw "Trust audit did not reject a VerifiedProgram hidden in a container."
    }

    $flatCtorNegativeProbe = @(
        "import Tests.Foundation",
        "open Grass",
        "axiom AuditProbe.Source._flat_ctor : Nonempty (VerifiedProgram Grass.Tests.Foundation.spec)",
        "noncomputable def AuditProbe.Sink._flat_ctor : ByteArray := emitProgram (Classical.choice AuditProbe.Source._flat_ctor)",
        "#audit_verified_programs"
    )
    [System.IO.File]::WriteAllLines($temporaryPath, $flatCtorNegativeProbe)
    $flatCtorNegativeOutput = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -eq 0 -or
        -not ($flatCtorNegativeOutput -match "AuditProbe.Sink._flat_ctor.*AuditProbe.Source._flat_ctor")) {
        $flatCtorNegativeOutput | ForEach-Object { Write-Host $_ }
        throw "Trust audit ignored a user declaration named _flat_ctor."
    }

    $externalProbe = @(
        "import Tests.Foundation",
        "open Grass",
        "namespace ExternalAuditProbe",
        "axiom boxedVerifiedProgram : Nonempty (VerifiedProgram Grass.Tests.Foundation.spec)",
        "noncomputable def emittedBytes : ByteArray := emitProgram (Classical.choice boxedVerifiedProgram)",
        "end ExternalAuditProbe"
    )
    [System.IO.File]::WriteAllLines($externalProbePath, $externalProbe)
    $externalBuildOutput = @(& lake env lean $externalProbePath -o $externalProbeOlean 2>&1)
    if ($LASTEXITCODE -ne 0) {
        $externalBuildOutput | ForEach-Object { Write-Host $_ }
        throw "Could not compile the imported external trust-audit probe."
    }
    $externalConsumerProbe = @(
        "import $externalProbeModule",
        "#audit_verified_programs"
    )
    [System.IO.File]::WriteAllLines($temporaryPath, $externalConsumerProbe)
    $externalConsumerOutput = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -eq 0 -or
        -not ($externalConsumerOutput -match "ExternalAuditProbe.emittedBytes.*ExternalAuditProbe.boxedVerifiedProgram")) {
        $externalConsumerOutput | ForEach-Object { Write-Host $_ }
        throw "Trust audit ignored a wrapped producer from an imported external module."
    }

    $implementedByProbe = @(
        "namespace ExternalRuntimeAuditProbe",
        "unsafe def replacement (_ : ByteArray) : ByteArray := ByteArray.empty",
        "@[implemented_by replacement]",
        "def identityBytes (bytes : ByteArray) : ByteArray := bytes",
        "end ExternalRuntimeAuditProbe"
    )
    [System.IO.File]::WriteAllLines($runtimeProbePath, $implementedByProbe)
    $runtimeBuildOutput = @(& lake env lean $runtimeProbePath -o $runtimeProbeOlean 2>&1)
    if ($LASTEXITCODE -ne 0) {
        $runtimeBuildOutput | ForEach-Object { Write-Host $_ }
        throw "Could not compile the implemented_by trust-audit probe."
    }
    $runtimeConsumerProbe = @(
        "import $runtimeProbeModule",
        "import Tests.Foundation",
        "open Grass",
        "def ExternalRuntimeAuditProbe.emittedBytes",
        "    (verified : VerifiedProgram Grass.Tests.Foundation.spec) : ByteArray :=",
        "  ExternalRuntimeAuditProbe.identityBytes (emitProgram verified)",
        "#audit_runtime_dependencies ExternalRuntimeAuditProbe.emittedBytes"
    )
    [System.IO.File]::WriteAllLines($temporaryPath, $runtimeConsumerProbe)
    $runtimeConsumerOutput = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -eq 0 -or
        -not ($runtimeConsumerOutput -match "ExternalRuntimeAuditProbe.identityBytes.*implemented_by.*ExternalRuntimeAuditProbe.replacement")) {
        $runtimeConsumerOutput | ForEach-Object { Write-Host $_ }
        throw "Trust audit ignored an implemented_by replacement in the runtime dependency closure."
    }

    $externProbe = @(
        "namespace ExternalRuntimeAuditProbe",
        "@[extern `"grass_runtime_probe_identity`"]",
        "def identityBytes (bytes : ByteArray) : ByteArray := bytes",
        "end ExternalRuntimeAuditProbe"
    )
    [System.IO.File]::WriteAllLines($runtimeProbePath, $externProbe)
    $runtimeBuildOutput = @(& lake env lean $runtimeProbePath -o $runtimeProbeOlean 2>&1)
    if ($LASTEXITCODE -ne 0) {
        $runtimeBuildOutput | ForEach-Object { Write-Host $_ }
        throw "Could not compile the extern trust-audit probe."
    }
    $externConsumerProbe = @(
        "import $runtimeProbeModule",
        "import Tests.Foundation",
        "open Grass",
        "def ExternalRuntimeAuditConsumer.emittedBytes",
        "    (verified : VerifiedProgram Grass.Tests.Foundation.spec) : ByteArray :=",
        "  emitProgram verified"
    )
    [System.IO.File]::WriteAllLines($runtimeConsumerPath, $externConsumerProbe)
    $runtimeBuildOutput = @(& lake env lean $runtimeConsumerPath -o $runtimeConsumerOlean 2>&1)
    if ($LASTEXITCODE -ne 0) {
        $runtimeBuildOutput | ForEach-Object { Write-Host $_ }
        throw "Could not compile the extern importing-module trust-audit probe."
    }
    $externAuditProbe = @(
        "import $runtimeConsumerModule",
        "#audit_runtime_dependencies ExternalRuntimeAuditConsumer.emittedBytes"
    )
    [System.IO.File]::WriteAllLines($temporaryPath, $externAuditProbe)
    $runtimeConsumerOutput = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -eq 0 -or
        -not ($runtimeConsumerOutput -match "ExternalRuntimeAuditProbe.identityBytes.*extern")) {
        $runtimeConsumerOutput | ForEach-Object { Write-Host $_ }
        throw "Trust audit ignored an extern implementation in an ordinarily imported runtime module."
    }

    $csimpSourceProbe = @(
        "namespace ExternalRuntimeAuditSource",
        "def identityBytes (bytes : ByteArray) : ByteArray := bytes",
        "end ExternalRuntimeAuditSource"
    )
    [System.IO.File]::WriteAllLines($runtimeProbePath, $csimpSourceProbe)
    $runtimeBuildOutput = @(& lake env lean $runtimeProbePath -o $runtimeProbeOlean 2>&1)
    if ($LASTEXITCODE -ne 0) {
        $runtimeBuildOutput | ForEach-Object { Write-Host $_ }
        throw "Could not compile the scoped-csimp source probe."
    }
    $scopedCSimpProbe = @(
        "import $runtimeProbeModule",
        "namespace ExternalScopedCSimpProbe",
        "unsafe def runtimeReplacement (_ : ByteArray) : ByteArray := ByteArray.empty",
        "@[implemented_by runtimeReplacement]",
        "def replacement (bytes : ByteArray) : ByteArray := bytes",
        "theorem replacement_eq : ExternalRuntimeAuditSource.identityBytes = replacement := rfl",
        "end ExternalScopedCSimpProbe"
    )
    [System.IO.File]::WriteAllLines($csimpProbePath, $scopedCSimpProbe)
    $runtimeBuildOutput = @(& lake env lean $csimpProbePath -o $csimpProbeOlean 2>&1)
    if ($LASTEXITCODE -ne 0) {
        $runtimeBuildOutput | ForEach-Object { Write-Host $_ }
        throw "Could not compile the scoped-csimp replacement probe."
    }
    $scopedCSimpConsumer = @(
        "import $runtimeProbeModule",
        "import $csimpProbeModule",
        "import Tests.Foundation",
        "open Grass",
        "section",
        "attribute [local csimp] ExternalScopedCSimpProbe.replacement_eq",
        "def ExternalScopedCSimpProbe.emittedBytes",
        "    (verified : VerifiedProgram Grass.Tests.Foundation.spec) : ByteArray :=",
        "  ExternalRuntimeAuditSource.identityBytes (emitProgram verified)",
        "end"
    )
    [System.IO.File]::WriteAllLines($runtimeConsumerPath, $scopedCSimpConsumer)
    $runtimeBuildOutput = @(& lake env lean $runtimeConsumerPath -o $runtimeConsumerOlean 2>&1)
    if ($LASTEXITCODE -ne 0) {
        $runtimeBuildOutput | ForEach-Object { Write-Host $_ }
        throw "Could not compile the imported scoped-csimp consumer probe."
    }
    $scopedCSimpAudit = @(
        "import $runtimeConsumerModule",
        "#audit_runtime_dependencies ExternalScopedCSimpProbe.emittedBytes"
    )
    [System.IO.File]::WriteAllLines($temporaryPath, $scopedCSimpAudit)
    $runtimeConsumerOutput = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -eq 0 -or
        -not ($runtimeConsumerOutput -match "ExternalScopedCSimpProbe.(replacement.*implemented_by.*runtimeReplacement|runtimeReplacement.*unsafe)")) {
        $runtimeConsumerOutput | ForEach-Object { Write-Host $_ }
        throw "Trust audit ignored a scoped csimp replacement after its attribute state expired."
    }

    Write-Host "Trust audit passed for $reported declaration(s)."
}
finally {
    if ([System.IO.File]::Exists($temporaryPath)) {
        [System.IO.File]::Delete($temporaryPath)
    }
    if ([System.IO.File]::Exists($externalProbePath)) {
        [System.IO.File]::Delete($externalProbePath)
    }
    if ([System.IO.File]::Exists($externalProbeOlean)) {
        [System.IO.File]::Delete($externalProbeOlean)
    }
    if ([System.IO.File]::Exists($runtimeProbePath)) {
        [System.IO.File]::Delete($runtimeProbePath)
    }
    if ([System.IO.File]::Exists($runtimeProbeOlean)) {
        [System.IO.File]::Delete($runtimeProbeOlean)
    }
    if ([System.IO.File]::Exists($csimpProbePath)) {
        [System.IO.File]::Delete($csimpProbePath)
    }
    if ([System.IO.File]::Exists($csimpProbeOlean)) {
        [System.IO.File]::Delete($csimpProbeOlean)
    }
    if ([System.IO.File]::Exists($runtimeConsumerPath)) {
        [System.IO.File]::Delete($runtimeConsumerPath)
    }
    if ([System.IO.File]::Exists($runtimeConsumerOlean)) {
        [System.IO.File]::Delete($runtimeConsumerOlean)
    }
}
