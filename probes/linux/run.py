"""Build and run bounded Linux direct-syscall and libc syscall(2) comparisons."""
import hashlib
import json
import os
import platform
import subprocess
import sys
import tempfile
import time
from pathlib import Path

CASES = ("raw_write", "libc_write", "raw_write_badfd", "libc_write_badfd", "raw_read", "libc_read", "raw_number_high32")
PAYLOAD, READ_INPUT = b"grass-linux-syscall", b"read-boundary-input"

def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def text(value): return value.decode("utf-8", errors="replace") if isinstance(value, bytes) else (value or "")

def run_process(command, timeout, **kwargs):
    try:
        done = subprocess.run(command, capture_output=True, timeout=timeout, **kwargs)
        return {"status": "completed", "exit": done.returncode, "stdout": text(done.stdout), "stderr": text(done.stderr)}
    except subprocess.TimeoutExpired as caught:
        return {"status": "timeout", "exit": None, "stdout": text(caught.stdout), "stderr": text(caught.stderr), "timeout_seconds": timeout}
    except OSError as caught:
        return {"status": "launch_error", "exit": None, "stdout": "", "stderr": str(caught)}

def parse_record(value, expected_case):
    row = json.loads(value)
    required = {"case", "route", "operation", "requested", "result", "raw_error", "emitted"}
    if not isinstance(row, dict) or set(row) != required: raise ValueError("probe JSON fields differ from the required schema")
    if row["case"] != expected_case: raise ValueError("probe case differs from the requested case")
    expected_route = "direct_raw_assembly" if expected_case.startswith("raw_") else "libc_syscall_wrapper"
    if row["route"] != expected_route: raise ValueError("probe route differs from the requested case")
    if row["operation"] not in ("read", "write", "number_width"): raise ValueError("probe operation is invalid")
    for field in ("requested", "result", "raw_error", "emitted"):
        if type(row[field]) is not int: raise ValueError(f"probe {field} is not an integer")
    if row["requested"] < 0 or row["raw_error"] < 0 or row["emitted"] < 0: raise ValueError("probe count/error is negative")
    return row

def run_case(executable, name):
    record_read, record_write = os.pipe()
    try:
        try:
            child = subprocess.Popen([str(executable), name, str(record_write)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, pass_fds=(record_write,))
        except OSError as caught:
            return {"status": "launch_error", "exit": None, "stdout": "", "stderr": str(caught), "record": "", "child_pid": None}
        os.close(record_write); record_write = None
        try:
            stdout, stderr = child.communicate(input=READ_INPUT if name.endswith("read") else b"", timeout=3)
            status = "completed"
        except subprocess.TimeoutExpired:
            child.kill(); stdout, stderr = child.communicate(); status = "timeout"
        # The parent write end is closed before this bounded read, so EOF rejects a zero-record child.
        record = os.read(record_read, 4096)
        return {"status": status, "exit": child.returncode if status == "completed" else None, "stdout": text(stdout), "stderr": text(stderr), "record": text(record), "child_pid": child.pid}
    finally:
        os.close(record_read)
        if record_write is not None: os.close(record_write)

def violations(row, output, expected_pid=None):
    errors, success = [], row["result"] >= 0
    if row["operation"] == "number_width":
        if row["result"] != expected_pid or row["raw_error"] != 0 or row["emitted"] != 0:
            errors.append("high syscall-number result differs from the parent-observed child PID")
        return errors
    if row["operation"] == "write":
        if success and (row["result"] > row["requested"] or row["emitted"] != row["result"]): errors.append("successful write count relation failed")
        if output.encode() != PAYLOAD[:max(row["result"], 0)]: errors.append("write output is not the reported input prefix")
    else:
        if success and (row["result"] > row["requested"] or row["emitted"] != row["result"] or len(output.encode()) != row["emitted"]): errors.append("selected successful read count relation failed")
        if output.encode() != READ_INPUT[:max(row["emitted"], 0)]: errors.append("read output is not the emitted input prefix")
    if "badfd" in row["case"]:
        expected = -9 if row["route"] == "direct_raw_assembly" else -1
        if row["result"] != expected or row["raw_error"] != 9 or row["emitted"] != 0: errors.append("bad-fd result does not expose the expected raw/wrapper error distinction")
    return errors

def main():
    root = Path(__file__).resolve().parents[2]
    output = root / ".lake" / "linux-probes"; output.mkdir(parents=True, exist_ok=True)
    source, runner = root / "probes/linux/syscall_probe.c", Path(__file__).resolve()
    binary = Path(tempfile.mkdtemp(prefix="grass-linux-probe-")) / "syscall_probe"
    report = {"schema_version": 1, "generated_unix_seconds": int(time.time()), "scope": "native Linux direct syscall instruction and libc syscall(2) wrapper comparisons; not Grass artifacts or proof", "host": {"kernel": platform.release(), "architecture": platform.machine(), "platform": platform.platform()}, "inputs": {"source_sha256": sha256(source), "runner_sha256": sha256(runner)}, "build": {}, "cases": [], "exit_group": [], "negative_controls": [], "harness_controls": [], "coverage_gaps": ["No interruption, cancellation, concurrency, pointer-fault, or arbitrary failure-effect coverage.", "Small pipes do not force partial read/write completion.", "Only the executing Linux kernel and detected architecture are observed; AArch64 compilation/execution is conditional and unobserved on x86-64 hosts."], "harness_errors": []}
    def finish(code):
        (output / "results.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8"); print(json.dumps(report, indent=2)); return code
    timeout = run_process([sys.executable, "-c", "import time; time.sleep(2)"], .1)
    report["harness_controls"].append({"name": "timeout_wrapper", "passed": timeout["status"] == "timeout", "result": timeout})
    valid = {"case": "raw_write", "route": "direct_raw_assembly", "operation": "write", "requested": 1, "result": 1, "raw_error": 0, "emitted": 1}
    for name, value in (("malformed_json", "nope"), ("missing_field", json.dumps({"case": "raw_write"})), ("wrong_route", json.dumps({**valid, "route": "libc_syscall_wrapper"}))):
        try: parse_record(value, "raw_write"); passed = False
        except (ValueError, TypeError, json.JSONDecodeError): passed = True
        report["harness_controls"].append({"name": name, "passed": passed})
    compiler = os.environ.get("CC", "cc")
    version = run_process([compiler, "--version"], 10, text=True)
    build = run_process([compiler, "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2", str(source), "-o", str(binary)], 60, text=True)
    report["build"] = {"compiler": compiler, "version": version, "compiler_version": version["stdout"].splitlines()[0] if version["status"] == "completed" and version["exit"] == 0 else "", **build, "binary_path": str(binary), "status": "success" if build["status"] == "completed" and build["exit"] == 0 else "failure"}
    if version["status"] != "completed" or version["exit"] != 0: report["harness_errors"].append("compiler version query failed")
    if report["build"]["status"] != "success": report["harness_errors"].append("native probe compilation failed"); return finish(2)
    report["inputs"]["binary_sha256"] = sha256(binary)
    for name in CASES:
        execution = run_case(binary, name); row = {"case": name, **execution, "violations": []}
        if execution["status"] != "completed" or execution["exit"] != 0: row["violations"].append("probe execution failure")
        else:
            try:
                observed = parse_record(execution["record"], name); row.update(observed); row["violations"] = violations(observed, execution["stdout"], execution["child_pid"])
            except (ValueError, TypeError, json.JSONDecodeError) as error: row["violations"].append(f"record parse failure: {error}")
        report["cases"].append(row)
    missing = run_case(binary, "raw_missing_record_control")
    try: parse_record(missing["record"], "raw_missing_record_control"); rejected = False
    except (ValueError, TypeError, json.JSONDecodeError): rejected = True
    report["harness_controls"].append({"name": "missing_record_child", "passed": missing["status"] == "completed" and missing["exit"] == 0 and missing["record"] == "" and rejected, "result": missing})
    for name in ("raw_exit_group", "libc_exit_group"):
        run = run_process([str(binary), name, "-1"], 3)
        report["exit_group"].append({"case": name, "parent_observed_exit": run["exit"], "passed": run["status"] == "completed" and run["exit"] == 37, "result": run})
    successful = next((row for row in report["cases"] if row.get("case") == "raw_write" and "result" in row), None)
    if successful:
        mutations = [({"result": successful["requested"] + 1}, successful["stdout"]), ({"emitted": successful["result"] - 1}, successful["stdout"]), ({"observed_output": "wrong_prefix"}, "!" + successful["stdout"][1:])]
        for mutation, observed_output in mutations:
            changed = {k: v for k, v in mutation.items() if k != "observed_output"}
            report["negative_controls"].append({"mutation": mutation, "violations": violations({**successful, **changed}, observed_output, successful["child_pid"])})
    else: report["harness_errors"].append("raw write observation unavailable for negative controls")
    failed = report["harness_errors"] or any(row["violations"] for row in report["cases"]) or any(not row["passed"] for row in report["exit_group"]) or any(not row["passed"] for row in report["harness_controls"]) or any(not row["violations"] for row in report["negative_controls"])
    return finish(1 if failed else 0)

if __name__ == "__main__": sys.exit(main())
