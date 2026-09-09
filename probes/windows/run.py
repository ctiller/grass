"""Build native probes and challenge the bounded synchronous WriteFile model."""
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from pathlib import Path

CASES = ("success", "zero", "invalid", "broken", "partial")

def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def output_text(value):
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def parse_observation(text, expected_case):
    observed = json.loads(text)
    if not isinstance(observed, dict):
        raise ValueError("probe JSON is not an object")
    required = {"case", "requested", "bool", "count", "last_error", "observed",
                "read_ok", "prefix_matches"}
    if set(observed) != required:
        raise ValueError("probe JSON fields differ from the required schema")
    if observed["case"] != expected_case:
        raise ValueError("probe case differs from the requested case")
    for field in ("requested", "count", "last_error", "observed"):
        value = observed[field]
        if type(value) is not int or value < 0 or value > 0xFFFFFFFF:
            raise ValueError(f"probe field {field} is not a DWORD-range integer")
    if type(observed["bool"]) is not int or not -(2 ** 31) <= observed["bool"] < 2 ** 31:
        raise ValueError("probe bool is not a signed 32-bit integer")
    for field in ("read_ok", "prefix_matches"):
        if type(observed[field]) is not bool:
            raise ValueError(f"probe field {field} is not a JSON boolean")
    return observed

def violations(row):
    errors = []
    succeeded = row["bool"] != 0
    if succeeded:
        if row["count"] > row["requested"]:
            errors.append("successful count exceeds request")
        if row["observed"] != row["count"]:
            errors.append("reported success count differs from pipe observation")
    if row["observed"] > row["requested"] or not row["prefix_matches"]:
        errors.append("observation is not a bounded input prefix")
    if not row["read_ok"]:
        errors.append("pipe observation failed")
    if row["case"] in ("invalid", "broken") and (succeeded or row["count"] != 0):
        errors.append("failure fixture did not return FALSE with zeroed count")
    if row["case"] == "success" and (not succeeded or row["count"] != row["requested"]):
        errors.append("small successful pipe write was not covered")
    return errors

def run_process(command, **kwargs):
    try:
        done = subprocess.run(command, text=True, capture_output=True, **kwargs)
        return {"status": "completed", "exit": done.returncode,
                "stdout": output_text(done.stdout), "stderr": output_text(done.stderr)}
    except subprocess.TimeoutExpired as error:
        return {"status": "timeout", "exit": None, "stdout": output_text(error.stdout),
                "stderr": output_text(error.stderr),
                "timeout_seconds": kwargs.get("timeout")}
    except OSError as error:
        return {"status": "launch_error", "exit": None, "stdout": "", "stderr": str(error)}

def main():
    root = Path(__file__).resolve().parents[2]
    output = root / ".lake" / "windows-probes"
    output.mkdir(parents=True, exist_ok=True)
    result_path = output / "results.json"
    source, runner = root / "probes/windows/writefile.c", Path(__file__).resolve()
    report = {"schema_version": 1, "generated_unix_seconds": int(time.time()),
        "scope": "MSVC-built native synchronous pipe API probes; not Grass-emitted artifacts or proof",
        "host": {"os": platform.platform(), "windows_version": platform.win32_ver(), "machine": platform.machine(),
                 "processor": platform.processor(), "processor_identifier": os.environ.get("PROCESSOR_IDENTIFIER", "")},
        "inputs": {"source_sha256": sha256(source), "runner_sha256": sha256(runner)},
        "build": {"status": "not_started"}, "cases": [], "negative_controls": [], "harness_controls": [],
        "coverage": {"strict_partial_success": False, "nonempty_zero_progress_success": False}, "harness_errors": []}
    def finish(code):
        result_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(report, indent=2))
        return code
    if os.name != "nt":
        report["harness_errors"].append("This probe requires Windows")
        return finish(2)
    try:
        timeout_control = run_process(
            [sys.executable, "-c", "import sys,time; print('timeout-output', flush=True); time.sleep(5)"],
            timeout=0.2)
        timeout_passed = (timeout_control["status"] == "timeout"
                          and timeout_control["stdout"].strip() == "timeout-output")
        report["harness_controls"].append(
            {"name": "timeout_output_serialization", "passed": timeout_passed,
             "result": timeout_control})
        valid_shape = {"case": "success", "requested": 1, "bool": 1, "count": 1,
                       "last_error": 0, "observed": 1,
                       "read_ok": True, "prefix_matches": True}
        malformed_controls = [
            ("malformed_json", "not-json", "success", None),
            ("missing_fields", '{"case":"success"}', "success", None),
            ("wrong_case", json.dumps({**valid_shape, "case": "zero"}), "success",
             "probe case differs from the requested case"),
            ("wrong_types", json.dumps({**valid_shape, "bool": True}), "success", None),
        ]
        for name, text, expected_case, expected_error in malformed_controls:
            try:
                parse_observation(text, expected_case)
                rejected = False
                error = ""
            except (json.JSONDecodeError, TypeError, ValueError) as caught:
                rejected = True
                error = str(caught)
            passed = rejected and (expected_error is None or error == expected_error)
            report["harness_controls"].append(
                {"name": name, "passed": passed, "rejection": error})
        vswhere = Path(os.environ["ProgramFiles(x86)"]) / "Microsoft Visual Studio/Installer/vswhere.exe"
        discovery = run_process([str(vswhere), "-latest", "-products", "*", "-requires",
            "Microsoft.VisualStudio.Component.VC.Tools.x86.x64", "-property", "installationPath"], timeout=15)
        report["build"]["discovery"] = discovery
        installation = discovery["stdout"].strip() if discovery["status"] == "completed" and discovery["exit"] == 0 else ""
        if not installation:
            report["build"]["status"] = "setup_failure"
            report["harness_errors"].append("MSVC x64 tools not found")
            return finish(2)
        report["build"]["compiler_installation"] = installation
        batch = output / "build.cmd"
        batch.write_text('@echo off\ncall "' + installation + '/Common7/Tools/VsDevCmd.bat" -no_logo -arch=x64\n'
            'if errorlevel 1 exit /b %errorlevel%\ncl /nologo /Bv /W4 /WX /O2 "' + str(source) +
            '" /Fe:writefile.exe /Fo:writefile.obj\n', encoding="utf-8")
        build = run_process([os.environ["COMSPEC"], "/d", "/c", str(batch)], cwd=output, timeout=60)
        report["build"].update(build)
        report["build"]["status"] = "success" if build["status"] == "completed" and build["exit"] == 0 else "failure"
        (output / "build.log").write_text(build["stdout"] + build["stderr"], encoding="utf-8")
        if report["build"]["status"] != "success":
            report["harness_errors"].append("native probe compilation failed")
            return finish(2)
        executable = output / "writefile.exe"
        report["inputs"]["binary_sha256"] = sha256(executable)
        for case in CASES:
            execution = run_process([str(executable), case], timeout=5)
            row = {"case": case, **execution, "violations": []}
            if execution["status"] != "completed" or execution["exit"] != 0:
                row["violations"].append("probe setup/execution failure")
            else:
                try:
                    observed = parse_observation(execution["stdout"], case)
                    row.update(observed)
                    row["violations"] = violations(observed)
                except (json.JSONDecodeError, TypeError, ValueError) as error:
                    row["parse_error"] = str(error)
                    row["violations"].append("probe output parse failure")
            report["cases"].append(row)
        usable = [r for r in report["cases"] if "bool" in r]
        success = next((r for r in usable if r["case"] == "success"), None)
        if success:
            for change in ({"count": success["requested"] + 1}, {"prefix_matches": False}, {"observed": success["observed"] - 1}):
                report["negative_controls"].append({"mutation": change, "violations": violations({**success, **change})})
        else:
            report["harness_errors"].append("success observation unavailable for negative controls")
        report["coverage"] = {
            "strict_partial_success": any(r["bool"] != 0 and 0 < r["count"] < r["requested"] for r in usable),
            "nonempty_zero_progress_success": any(r["bool"] != 0 and r["requested"] > 0 and r["count"] == 0 for r in usable),
        }
    except Exception as error:
        report["harness_errors"].append(f"unexpected harness failure: {type(error).__name__}: {error}")
        return finish(2)
    failed = (report["harness_errors"]
              or any(r["violations"] for r in report["cases"])
              or any(not c["violations"] for c in report["negative_controls"])
              or any(not c["passed"] for c in report["harness_controls"]))
    return finish(1 if failed else 0)

if __name__ == "__main__":
    sys.exit(main())
