# The program body is Grass. This host launcher records a bounded native sample.
$ErrorActionPreference = 'Stop'
if ([Environment]::OSVersion.Platform -ne [PlatformID]::Win32NT) {
    throw 'This launcher requires Windows.'
}
$repoRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '../..')).Path
$probeDirectory = Join-Path $repoRoot '.lake/grass-windows-probes'
[IO.Directory]::CreateDirectory($probeDirectory) | Out-Null
$imagePath = Join-Path $probeDirectory 'hello.exe'
$expectedPath = Join-Path $probeDirectory 'expected-stdout.bin'
Push-Location -LiteralPath $repoRoot
try {
    & lake build Tests.Platform.Win32LoaderEntry
    if ($LASTEXITCODE -ne 0) { throw 'Grass loader fixture build failed.' }
    & lake env lean --run Tools/EmitGrassHello.lean $imagePath $expectedPath
    if ($LASTEXITCODE -ne 0) { throw 'Grass PE emission failed.' }

    $startInfo = [Diagnostics.ProcessStartInfo]::new()
    $startInfo.FileName = $imagePath
    $startInfo.WorkingDirectory = $probeDirectory
    $startInfo.UseShellExecute = $false
    $startInfo.CreateNoWindow = $true
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    $process = [Diagnostics.Process]::new()
    $process.StartInfo = $startInfo
    $outputBytes = [IO.MemoryStream]::new()
    $errorBytes = [IO.MemoryStream]::new()
    try {
        if (-not $process.Start()) { throw 'Windows did not start the Grass image.' }
        $byteLimit = 4096
        $readers = @(
            @{ stream = $process.StandardOutput.BaseStream; captured = $outputBytes; buffer = [byte[]]::new(1024); pending = $null; ended = $false },
            @{ stream = $process.StandardError.BaseStream; captured = $errorBytes; buffer = [byte[]]::new(1024); pending = $null; ended = $false }
        )
        $timer = [Diagnostics.Stopwatch]::StartNew()
        $timedOut = $false
        $outputLimitExceeded = $false
        while ($true) {
            foreach ($reader in $readers) {
                if ($reader.ended) { continue }
                if ($null -eq $reader.pending) {
                    $reader.pending = $reader.stream.ReadAsync($reader.buffer, 0, $reader.buffer.Length)
                }
                if (-not $reader.pending.IsCompleted) { continue }
                $count = $reader.pending.GetAwaiter().GetResult()
                $reader.pending = $null
                if ($count -eq 0) { $reader.ended = $true; continue }
                $remaining = $byteLimit - $reader.captured.Length
                $reader.captured.Write($reader.buffer, 0, [Math]::Min($count, $remaining))
                if ($count -gt $remaining) { $outputLimitExceeded = $true }
            }
            if ($outputLimitExceeded) { break }
            if ($process.HasExited -and $readers[0].ended -and $readers[1].ended) { break }
            if ($timer.ElapsedMilliseconds -ge 10000) { $timedOut = $true; break }
            [Threading.Thread]::Sleep(10)
        }
        if ($timedOut -or $outputLimitExceeded) {
            if (-not $process.HasExited) { $process.Kill($true) }
            if (-not $process.WaitForExit(2000)) { throw 'Probe termination did not complete.' }
        }
        $actual = $outputBytes.ToArray()
        $expected = [IO.File]::ReadAllBytes($expectedPath)
        $matches = [Convert]::ToBase64String($actual) -ceq [Convert]::ToBase64String($expected)
        $result = [ordered]@{
            kind = 'grass-source-native-loader-sample'
            os = [Runtime.InteropServices.RuntimeInformation]::OSDescription
            architecture = [Runtime.InteropServices.RuntimeInformation]::OSArchitecture.ToString()
            sourceSha256 = (Get-FileHash -LiteralPath (Join-Path $repoRoot 'Spikes/1_Hello_World/Program.lean')).Hash
            imageSha256 = (Get-FileHash -LiteralPath $imagePath).Hash
            imageSize = (Get-Item -LiteralPath $imagePath).Length
            timedOut = $timedOut
            streamByteLimit = $byteLimit
            outputLimitExceeded = $outputLimitExceeded
            exitCode = $process.ExitCode
            stdoutBase64 = [Convert]::ToBase64String($actual)
            stderrBase64 = [Convert]::ToBase64String($errorBytes.ToArray())
            stdoutMatches = $matches
            passed = (-not $timedOut) -and (-not $outputLimitExceeded) -and ($process.ExitCode -eq 0) -and $matches -and ($errorBytes.Length -eq 0)
        }
        $result | ConvertTo-Json | Set-Content -LiteralPath (Join-Path $probeDirectory 'result.json') -Encoding utf8
        $result | ConvertTo-Json
        if (-not $result.passed) { throw 'Grass native sample disagreed with expected output/exit.' }
    } finally {
        $process.Dispose()
        $outputBytes.Dispose()
        $errorBytes.Dispose()
    }
} finally {
    Pop-Location
}
