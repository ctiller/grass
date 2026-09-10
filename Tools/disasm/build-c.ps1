param(
    [Parameter(Mandatory = $true)][string]$CompilerDirectory,
    [string]$OutputDirectory = ".lake/disasm/c"
)
$ErrorActionPreference = "Stop"
$repo = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot "../.."))
$output = [IO.Path]::GetFullPath((Join-Path $repo $OutputDirectory))
$compiler = Join-Path $CompilerDirectory "cl.exe"
$linker = Join-Path $CompilerDirectory "link.exe"
$dumper = Join-Path $CompilerDirectory "dumpbin.exe"
foreach ($tool in @($compiler, $linker, $dumper)) {
    if (!(Test-Path -LiteralPath $tool -PathType Leaf)) { throw "Missing tool: $tool" }
}
New-Item -ItemType Directory -Force -Path $output | Out-Null
$revision = & git -C $repo rev-parse HEAD
if ($LASTEXITCODE -ne 0) { throw "Could not identify repository revision" }
$records = @()
foreach ($case in @("store_safe", "store_oob")) {
    $source = Join-Path $repo "Tests/Disasm/C/$case.c"
    $object = Join-Path $output "$case.obj"
    $binary = Join-Path $output "$case.exe"
    $compileArgs = @("/nologo", "/c", "/O2", "/GS-", "/Fo$object", $source)
    & $compiler @compileArgs
    if ($LASTEXITCODE -ne 0) { throw "Compilation failed: $case" }
    $linkArgs = @("/nologo", "/entry:probe", "/subsystem:console", "/nodefaultlib", "/fixed",
        "/machine:x64", "/out:$binary", $object)
    & $linker @linkArgs
    if ($LASTEXITCODE -ne 0) { throw "Link failed: $case" }
    $library = Join-Path $output "$case.dll"
    $libraryArgs = @("/nologo", "/dll", "/noentry", "/export:probe", "/nodefaultlib",
        "/machine:x64", "/out:$library", $object)
    & $linker @libraryArgs
    if ($LASTEXITCODE -ne 0) { throw "Callable DLL link failed: $case" }
    $disassembly = & $dumper /nologo /disasm $binary
    if ($LASTEXITCODE -ne 0) { throw "Independent disassembly failed: $case" }
    $disassembly | Set-Content -LiteralPath (Join-Path $output "$case.dumpbin.txt")
    $libraryDisassembly = & $dumper /nologo /disasm $library
    if ($LASTEXITCODE -ne 0) { throw "Independent DLL disassembly failed: $case" }
    $libraryDisassembly | Set-Content -LiteralPath (Join-Path $output "$case.dll.dumpbin.txt")
    $libraryExports = & $dumper /nologo /exports $library
    if ($LASTEXITCODE -ne 0) { throw "Independent DLL export listing failed: $case" }
    $libraryExports | Set-Content -LiteralPath (Join-Path $output "$case.dll.exports.txt")
    $records += [ordered]@{
        case = $case
        source = "Tests/Disasm/C/$case.c"
        sourceSha256 = (Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash
        binary = "$case.exe"
        binarySha256 = (Get-FileHash -LiteralPath $binary -Algorithm SHA256).Hash
        library = "$case.dll"
        librarySha256 = (Get-FileHash -LiteralPath $library -Algorithm SHA256).Hash
        libraryDisassembly = "$case.dll.dumpbin.txt"
        libraryExports = "$case.dll.exports.txt"
        byteLength = (Get-Item -LiteralPath $binary).Length
        compileArguments = $compileArgs
        linkArguments = $linkArgs
        libraryArguments = $libraryArgs
    }
}
[ordered]@{
    schema = "grass.disasm.c-build.v1"
    revision = $revision
    compilerVersion = (Get-Item -LiteralPath $compiler).VersionInfo.FileVersion
    linkerVersion = (Get-Item -LiteralPath $linker).VersionInfo.FileVersion
    scope = "callable attempted store under live writable 8-byte RCX object contract; not process startup"
    assurance = "compiler artifacts and independent disassembly only; no safety verdict"
    fixtures = $records
} | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath (Join-Path $output "manifest.json")
Write-Output "Built controlled C fixtures in $output. No fixture binary was executed."
