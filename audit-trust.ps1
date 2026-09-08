[CmdletBinding()]
param(
    [string[]]$LibrarySourceRoot = @("Grass"),
    [string[]]$TestSourceRoot = @("Tests"),
    [string[]]$Declaration = @(
        "Grass.StableId.render_of_empty_namespace",
        "Grass.RequirementKind.extension_injective",
        "Grass.DemandCertificateFamily.get",
        "Grass.ObservationProjection.ext",
        "Grass.ObservationProjection.identity_project",
        "Grass.ObservationProjection.comp_project",
        "Grass.ObservationProjection.identity_comp",
        "Grass.ObservationProjection.comp_identity",
        "Grass.ObservationProjection.comp_assoc",
        "Grass.RelationalSystem.Steps.trans",
        "Grass.RelationalSystem.Steps.graphExtends",
        "Grass.RelationalSystem.InfiniteContinuation.ext",
        "Grass.RelationalSystem.InfiniteContinuation.graphExtendsAt",
        "Grass.RelationalSystem.InfiniteContinuation.prefixSteps",
        "Grass.RelationalSystem.Runs.initialValid",
        "Grass.RelationalSystem.Runs.steps",
        "Grass.RelationalSystem.Runs.ofInitialSteps",
        "Grass.RelationalSystem.Runs.append",
        "Grass.RelationalSystem.Runs.graphExtends",
        "Grass.RelationalSystem.ExecutionPrefix.ext",
        "Grass.RelationalSystem.ExecutionPrefix.append_refl",
        "Grass.RelationalSystem.ExecutionPrefix.append_assoc",
        "Grass.RelationalSystem.ExecutionPrefix.step_eq_append",
        "Grass.BehaviorRefinement.ext",
        "Grass.BehaviorRefinement.refl_trans",
        "Grass.BehaviorRefinement.trans_refl",
        "Grass.BehaviorRefinement.trans_assoc",
        "Grass.BehaviorRefinement.mapSteps",
        "Grass.BehaviorRefinement.mapInfinite",
        "Grass.BehaviorRefinement.mapInfinite_refl",
        "Grass.BehaviorRefinement.mapInfinite_trans",
        "Grass.BehaviorRefinement.mapCompletion",
        "Grass.BehaviorRefinement.mapCompletion_refl",
        "Grass.BehaviorRefinement.mapCompletion_trans",
        "Grass.BehaviorRefinement.mapRuns",
        "Grass.BehaviorRefinement.mapPrefix_refl",
        "Grass.BehaviorRefinement.mapPrefix_initial",
        "Grass.BehaviorRefinement.mapPrefix_trans",
        "Grass.BehaviorRefinement.mapPrefix_step",
        "Grass.BehaviorRefinement.mapPrefix_append",
        "Grass.BehaviorRefinement.mapPrefix_events",
        "Grass.BehaviorRefinement.observe_mapPrefix",
        "Grass.BehaviorRefinement.inputOf_mapPrefix",
        "Grass.BehaviorRefinement.hasInput_mapPrefix",
        "Grass.BehaviorRefinement.terminal_mapPrefix",
        "Grass.BehaviorRefinement.mapCompletionAtPrefix",
        "Grass.BehaviorRefinement.mapCompletionAtPrefix_refl",
        "Grass.BehaviorRefinement.mapCompletionAtPrefix_trans",
        "Grass.BehaviorRefinement.preservesAcceptance",
        "Grass.VerifiedProgram.loadedBehavior_exact",
        "Grass.VerifiedProgram.loadedAdequate",
        "Grass.VerifiedProgram.sound",
        "Grass.VerifiedProgram.execution_nonempty",
        "Grass.VerifiedProgram.execution_completes",
        "Grass.VerifiedProgram.CompletionRefinement",
        "Grass.VerifiedProgram.completion_refinement_nonempty",
        "Grass.emitProgram_parses"
    ),
    [string[]]$AllowedAxiom = @(
        "propext",
        "Classical.choice",
        "Quot.sound"
    )
)

$ErrorActionPreference = "Stop"

function Get-PathUnder([string] $Base, [string] $Full) {
    # [IO.Path]::GetRelativePath is unavailable on Windows PowerShell 5.1.
    # Every caller supplies a path discovered underneath Base, so a checked
    # prefix removal is both portable and fail-closed.
    $normalizedBase = [IO.Path]::GetFullPath($Base).TrimEnd('\', '/')
    $normalizedFull = [IO.Path]::GetFullPath($Full)
    $separator = [IO.Path]::DirectorySeparatorChar
    $comparison = [StringComparison]::Ordinal
    if ($separator -eq '\') {
        $comparison = [StringComparison]::OrdinalIgnoreCase
    }
    if (-not $normalizedFull.StartsWith($normalizedBase + $separator, $comparison)) {
        throw "$normalizedFull is not underneath $normalizedBase"
    }
    return $normalizedFull.Substring($normalizedBase.Length + 1).Replace('\', '/')
}

function Get-RejectedAxiom(
    [string[]] $Used,
    [string[]] $Allowed
) {
    # Lean names require ordinal equality. Even PowerShell's case-sensitive
    # comparison operators use culture-sensitive string comparison, which can
    # equate distinct Unicode spellings.
    $rejected = @()
    foreach ($usedAxiom in $Used) {
        $accepted = $false
        foreach ($allowedAxiom in $Allowed) {
            if ([String]::Equals($usedAxiom, $allowedAxiom, [StringComparison]::Ordinal)) {
                $accepted = $true
                break
            }
        }
        if (-not $accepted) {
            $rejected += $usedAxiom
        }
    }
    return @($rejected)
}

if ($Declaration.Count -eq 0) {
    throw "At least one declaration must be audited."
}

$caseVariantProbe = @(Get-RejectedAxiom -Used @("Propext") -Allowed @("propext"))
if ($caseVariantProbe.Count -ne 1 -or
    -not [String]::Equals($caseVariantProbe[0], "Propext", [StringComparison]::Ordinal)) {
    throw "Axiom allowlist comparison is not ordinal."
}

$moduleNames = @()
$entrypointModuleNames = @()
$topLevelMainPattern =
    '(?m)^[\t ]*(?:(?:unsafe|partial|noncomputable)[\t ]+)*def[\t ]+main(?:[\t ]|:)'
foreach ($root in $LibrarySourceRoot) {
    if (-not (Test-Path -LiteralPath $root -PathType Container)) {
        throw "Configured library source root '$root' does not exist."
    }
    foreach ($file in Get-ChildItem -LiteralPath $root -Filter '*.lean' -File -Recurse) {
        $relative = Get-PathUnder (Get-Location).Path $file.FullName
        $withoutExtension = $relative.Substring(0, $relative.Length - '.lean'.Length)
        $moduleNames += $withoutExtension.Replace('/', '.')
    }
}
foreach ($root in $TestSourceRoot) {
    if (-not (Test-Path -LiteralPath $root -PathType Container)) {
        throw "Configured test source root '$root' does not exist."
    }
    foreach ($file in Get-ChildItem -LiteralPath $root -Filter '*.lean' -File -Recurse) {
        $relative = Get-PathUnder (Get-Location).Path $file.FullName
        $withoutExtension = $relative.Substring(0, $relative.Length - '.lean'.Length)
        $moduleName = $withoutExtension.Replace('/', '.')
        $source = Get-Content -LiteralPath $file.FullName -Raw

        # Executable test modules intentionally share Lean's required top-level
        # runner name `main`, so importing two of them into one environment is
        # impossible. Audit each such module separately below. A false positive
        # only creates an extra audit pass; a missed entrypoint makes the aggregate
        # import fail, so this partition cannot silently drop a module.
        if ($source -match $topLevelMainPattern) {
            $entrypointModuleNames += $moduleName
        }
        else {
            $moduleNames += $moduleName
        }
    }
}
$moduleNames = @($moduleNames | Sort-Object -Unique)
$entrypointModuleNames = @($entrypointModuleNames | Sort-Object -Unique)

$temporaryPath = [System.IO.Path]::Combine(
    [System.IO.Path]::GetTempPath(),
    "grass-axiom-audit-$([System.Guid]::NewGuid().ToString('N')).lean"
)
$externalProbeModule = "AuditExternalProbe$([System.Guid]::NewGuid().ToString('N'))"
$externalProbePath = Join-Path (Get-Location).Path "$externalProbeModule.lean"
$externalProbeOlean = Join-Path (Get-Location).Path ".lake/build/lib/lean/$externalProbeModule.olean"
$internalRootProbeModule = "AuditInternalRootProbe$([System.Guid]::NewGuid().ToString('N'))"
$internalRootProbePath = Join-Path (Get-Location).Path "$internalRootProbeModule.lean"
$internalRootProbeOlean = Join-Path (Get-Location).Path ".lake/build/lib/lean/$internalRootProbeModule.olean"
$runtimeProbeModule = "AuditRuntimeProbe$([System.Guid]::NewGuid().ToString('N'))"
$runtimeProbePath = Join-Path (Get-Location).Path "$runtimeProbeModule.lean"
$runtimeProbeOlean = Join-Path (Get-Location).Path ".lake/build/lib/lean/$runtimeProbeModule.olean"
$csimpProbeModule = "AuditScopedCSimpProbe$([System.Guid]::NewGuid().ToString('N'))"
$csimpProbePath = Join-Path (Get-Location).Path "$csimpProbeModule.lean"
$csimpProbeOlean = Join-Path (Get-Location).Path ".lake/build/lib/lean/$csimpProbeModule.olean"
$runtimeConsumerModule = "AuditRuntimeConsumer$([System.Guid]::NewGuid().ToString('N'))"
$runtimeConsumerPath = Join-Path (Get-Location).Path "$runtimeConsumerModule.lean"
$runtimeConsumerOlean = Join-Path (Get-Location).Path ".lake/build/lib/lean/$runtimeConsumerModule.olean"
$auditNonce = [System.Guid]::NewGuid().ToString('N')
$auditCommand = "grass_trust_audit_$auditNonce"
$auditMarker = "grass-trust-audit-complete:$auditNonce"
$auditMarkerPattern = [regex]::Escape($auditMarker)
$auditInvocation = @(
    "open Lean Elab Command",
    "elab `"#$auditCommand`" : command => do",
    "  Grass.Trust.auditVerifiedPrograms",
    "  logInfo `"$auditMarker`"",
    "#$auditCommand"
)

try {
    $commands = @($moduleNames | ForEach-Object { "import $_" })
    $commands += $auditInvocation
    $commands += $Declaration | ForEach-Object { "#print axioms $_" }
    [System.IO.File]::WriteAllLines($temporaryPath, $commands)

    $output = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -ne 0) {
        $output | ForEach-Object { Write-Error $_ }
        throw "Lean could not audit the requested declaration closure."
    }
    if (-not ($output -match $auditMarkerPattern)) {
        throw "Lean did not execute the generated trust-audit driver."
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
            $rejected = @(Get-RejectedAxiom -Used $used -Allowed $AllowedAxiom)
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

    foreach ($entrypointModule in $entrypointModuleNames) {
        Write-Host "Auditing executable test module '$entrypointModule'."
        $entrypointCommands = @(
            "import Tests.Foundation",
            "import $entrypointModule"
        )
        $entrypointCommands += $auditInvocation
        [System.IO.File]::WriteAllLines($temporaryPath, $entrypointCommands)

        $entrypointOutput = @(& lake env lean $temporaryPath 2>&1)
        if ($LASTEXITCODE -ne 0 -or
            -not ($entrypointOutput -match $auditMarkerPattern)) {
            $entrypointOutput | ForEach-Object { Write-Error $_ }
            throw "Trust audit failed for executable test module '$entrypointModule'."
        }
        $entrypointOutput | ForEach-Object { Write-Host $_ }
    }

    $rootNonvacuityProbe = @(
        "import Grass.Trust.Audit",
        "open Grass",
        "def passthrough {spec : SpecProcess} (verified : VerifiedProgram spec) : VerifiedProgram spec := verified",
        "#audit_verified_programs"
    )
    [System.IO.File]::WriteAllLines($temporaryPath, $rootNonvacuityProbe)
    $rootNonvacuityOutput = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -eq 0 -or
        -not ($rootNonvacuityOutput -match "trust audit found no concrete VerifiedProgram declarations")) {
        $rootNonvacuityOutput | ForEach-Object { Write-Host $_ }
        throw "Trust audit accepted generated constructor machinery or a certificate pass-through as a concrete root."
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

    $internalRootProbe = @(
        "import Tests.Foundation",
        "open Grass",
        "namespace InternalRootAuditProbe",
        "@[irreducible] def HiddenVerifiedProgram : Type 1 := VerifiedProgram Grass.Tests.Foundation.spec",
        "def _hiddenVerifiedProgram : HiddenVerifiedProgram := by",
        "  unfold HiddenVerifiedProgram",
        "  exact Grass.Tests.Foundation.verified",
        "def _flat_ctor : HiddenVerifiedProgram := by",
        "  unfold HiddenVerifiedProgram",
        "  exact Grass.Tests.Foundation.verified",
        "inductive AuthoredContainer where | node",
        "def AuthoredContainer.node._flat_ctor : HiddenVerifiedProgram := by",
        "  unfold HiddenVerifiedProgram",
        "  exact Grass.Tests.Foundation.verified",
        "end InternalRootAuditProbe"
    )
    [System.IO.File]::WriteAllLines($internalRootProbePath, $internalRootProbe)
    $internalRootBuildOutput = @(& lake env lean $internalRootProbePath -o $internalRootProbeOlean 2>&1)
    if ($LASTEXITCODE -ne 0) {
        $internalRootBuildOutput | ForEach-Object { Write-Host $_ }
        throw "Could not compile the imported underscore-prefixed root probe."
    }
    $internalRootConsumerProbe = @(
        "import $internalRootProbeModule",
        "#audit_verified_programs"
    )
    [System.IO.File]::WriteAllLines($temporaryPath, $internalRootConsumerProbe)
    $internalRootConsumerOutput = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -ne 0 -or
        -not ($internalRootConsumerOutput -match "InternalRootAuditProbe\._hiddenVerifiedProgram") -or
        -not ($internalRootConsumerOutput -match "InternalRootAuditProbe\._flat_ctor") -or
        -not ($internalRootConsumerOutput -match "InternalRootAuditProbe\.AuthoredContainer\.node\._flat_ctor")) {
        $internalRootConsumerOutput | ForEach-Object { Write-Host $_ }
        throw "Trust audit did not discover an imported authored underscore-prefixed root."
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

    $underscoreAxiomNegativeProbe = @(
        "import Tests.Foundation",
        "axiom Grass._unauditedFalse : False",
        "#audit_verified_programs"
    )
    [System.IO.File]::WriteAllLines($temporaryPath, $underscoreAxiomNegativeProbe)
    $underscoreAxiomNegativeOutput = @(& lake env lean $temporaryPath 2>&1)
    if ($LASTEXITCODE -eq 0 -or
        -not ($underscoreAxiomNegativeOutput -match "Grass\._unauditedFalse.*rejected axioms")) {
        $underscoreAxiomNegativeOutput | ForEach-Object { Write-Host $_ }
        throw "Trust audit ignored an authored underscore-prefixed axiom."
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

    Write-Host "Trust audit passed for $reported declaration(s) and $($entrypointModuleNames.Count) executable test module(s)."
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
    if ([System.IO.File]::Exists($internalRootProbePath)) {
        [System.IO.File]::Delete($internalRootProbePath)
    }
    if ([System.IO.File]::Exists($internalRootProbeOlean)) {
        [System.IO.File]::Delete($internalRootProbeOlean)
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

# Every failure path above terminates with `throw`, so reaching here means the
# audit passed -- and it must say so with an exit code, not just a message.
#
# `shell: pwsh` in .github/workflows/library.yml runs this script and then
# exits with `$LASTEXITCODE`. This script never called `exit`, so that code
# was whatever the last native command left behind, and the last native
# command on the success path is the scoped-csimp probe's `lake env lean`,
# which the audit requires to *fail*: the check immediately above passes only
# when `$LASTEXITCODE -ne 0`. Passing therefore guaranteed a non-zero exit.
#
# The `finally` block only calls .NET file methods, which do not touch
# `$LASTEXITCODE`, so nothing reset it before the wrapper read it.
#
# This gate had never once been green on main -- 39 of the last 39 runs
# failed -- while printing "Trust audit passed" as its final line every time.
# A gate that always fails hides a real regression exactly as well as a gate
# that always passes: there was no state it could report that anyone could
# tell apart from the state it was already in.
exit 0
