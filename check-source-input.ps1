$ErrorActionPreference = 'Stop'

# include_source_chars embeds the current authored file during elaboration. Lake does
# not track that file as an import, so a cached fixture is insufficient here.
# Run Lean directly on each source-backed fixture after building its imports.
Push-Location $PSScriptRoot
try {
    & lake build Grass.Assembly.SourceStore Grass.Assembly.X86ControlFlow Grass.Assembly.X86ClosedEncoding Grass.Assembly.X86BranchLayout Tests.Assembly.SourceLiteral
    if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    foreach ($fixture in @('Tests/Assembly/SourceInput.lean', 'Tests/Assembly/SourceStore.lean',
        'Tests/Assembly/X86Source.lean', 'Tests/Assembly/X86ControlFlow.lean',
        'Tests/Assembly/X86ClosedEncoding.lean', 'Tests/Assembly/X86BranchLayout.lean')) {
        & lake env lean $fixture
        if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
    }
} finally {
    Pop-Location
}
