param([string]$OutputDirectory = "$PSScriptRoot/../../target/x86-native")
$ErrorActionPreference = 'Stop'
$vswhere = "${env:ProgramFiles(x86)}/Microsoft Visual Studio/Installer/vswhere.exe"
$installation = & $vswhere -latest -products '*' -requires Microsoft.VisualStudio.Component.VC.Tools.x86.x64 -property installationPath
if (!$installation) { throw 'MSVC x64 tools are required' }
$vcvars = Join-Path $installation 'VC/Auxiliary/Build/vcvars64.bat'
$out = [IO.Path]::GetFullPath($OutputDirectory)
New-Item -ItemType Directory -Force -Path $out | Out-Null
$source = Join-Path $PSScriptRoot 'windows.c'
$batch = Join-Path $out 'build.cmd'
@"
@echo off
call "$vcvars" >nul
if errorlevel 1 exit /b 1
cl /nologo /W4 /WX /O2 /Fe:"$out/windows.exe" /Fo:"$out/windows.obj" "$source" /link /INCREMENTAL:NO
"@ | Set-Content -LiteralPath $batch -Encoding ascii
& cmd.exe /c $batch
if ($LASTEXITCODE -ne 0) { throw "native worker build failed: $LASTEXITCODE" }
