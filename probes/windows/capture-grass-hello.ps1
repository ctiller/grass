# Windows-only process capture; build/emission orchestration lives in Bash.
param(
    [Parameter(Mandatory)][string]$ImagePath,
    [Parameter(Mandatory)][string]$ExpectedPath,
    [Parameter(Mandatory)][string]$SourceSnapshotPath,
    [Parameter(Mandatory)][string]$ResultPath
)
$ErrorActionPreference = 'Stop'
if ([Environment]::OSVersion.Platform -ne [PlatformID]::Win32NT) {
    throw 'This launcher requires Windows.'
}
$ImagePath = (Resolve-Path -LiteralPath $ImagePath).Path
$probeDirectory = Split-Path -Parent $ImagePath
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
    $started = $false
    $result = $null
    try {
        if (-not $process.Start()) { throw 'Windows did not start the Grass image.' }
        $started = $true
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
            status = 'observed'
            os = [Runtime.InteropServices.RuntimeInformation]::OSDescription
            architecture = [Runtime.InteropServices.RuntimeInformation]::OSArchitecture.ToString()
            sourceSha256 = (Get-FileHash -LiteralPath $sourceSnapshotPath).Hash
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
        if ($result.passed) { $result.status = 'passed' }
        $result | ConvertTo-Json | Set-Content -LiteralPath $ResultPath -Encoding utf8
        $result | ConvertTo-Json
        if (-not $result.passed) { throw 'Grass native sample disagreed with expected output/exit.' }
    } catch {
        $captureError = $_
        $terminationError = $null
        if ($started -and (-not $process.HasExited)) {
            try {
                $process.Kill($true)
                if (-not $process.WaitForExit(2000)) { throw 'Probe termination did not complete.' }
            } catch {
                $terminationError = $_.Exception.Message
            }
        }
        if ($null -eq $result) { $result = [ordered]@{ kind = 'grass-source-native-loader-sample' } }
        $result['status'] = 'failed'
        $result['passed'] = $false
        $result['error'] = $captureError.Exception.Message
        $result['terminationError'] = $terminationError
        $result | ConvertTo-Json | Set-Content -LiteralPath $ResultPath -Encoding utf8
        throw $captureError
    } finally {
        $process.Dispose()
        $outputBytes.Dispose()
        $errorBytes.Dispose()
    }
