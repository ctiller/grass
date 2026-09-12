"""Independently inspect Lean-emitted ELF target fixtures and their e_phoff fields."""
import hashlib
import json
import os
import shutil
import struct
import subprocess
import sys
from pathlib import Path

FIXTURES = (("target-zero.elf", 0), ("target-one.elf", 1),
            ("target-two.elf", 2), ("target-three.elf", 3))
HEADER = struct.Struct("<16sHHIQQQIHHHHHH")
PROGRAM = struct.Struct("<IIQQQQQQ")


def text(value):
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value or ""


def command(argv):
    evidence = {"argv": list(map(str, argv))}
    try:
        done = subprocess.run(argv, capture_output=True, text=True, timeout=10,
                              env={**os.environ, "LC_ALL": "C"})
        return evidence | {"status": "completed", "exit": done.returncode,
                           "stdout": text(done.stdout), "stderr": text(done.stderr)}
    except subprocess.TimeoutExpired as error:
        return evidence | {"status": "timeout", "exit": None,
                           "stdout": text(error.stdout), "stderr": text(error.stderr)}
    except OSError as error:
        return evidence | {"status": "launch_error", "exit": None,
                           "stdout": "", "stderr": str(error)}


def check_bytes(data, count):
    if len(data) < HEADER.size:
        return {"passed": False, "error": "short ELF header"}
    ident, etype, machine, version, entry, phoff, shoff, flags, ehsize, phentsize, phnum, shentsize, shnum, shstrndx = HEADER.unpack(data[:HEADER.size])
    table_end = HEADER.size + PROGRAM.size * count
    expected_phoff = 0 if count == 0 else HEADER.size
    checks = {
        "exact_length": len(data) == table_end + 2 * count,
        "header": (ident == b"\x7fELF\x02\x01\x01" + b"\0" * 9 and
                   (etype, machine, version, entry, shoff, flags, ehsize, phentsize, phnum, shentsize, shnum, shstrndx) ==
                   (2, 183, 1, 0x400000, 0, 0, 64, 56, count, 0, 0, 0)),
        "e_phoff": phoff == expected_phoff,
        "table_bounds": count == 0 or (phoff == HEADER.size and phoff + PROGRAM.size * count == table_end <= len(data)),
    }
    headers = []
    for index in range(count):
        start = HEADER.size + PROGRAM.size * index
        ptype, pflags, poffset, vaddr, paddr, filesz, memsz, align = PROGRAM.unpack(data[start:start + PROGRAM.size])
        expected_offset = table_end + 2 * index
        passed = (ptype == 1 and pflags == 5 and poffset == expected_offset and
                  vaddr == paddr == 0x400000 and filesz == memsz == 2 and align == 0x1000)
        headers.append({"index": index, "p_type": ptype, "p_flags": pflags,
                        "p_offset": poffset, "p_filesz": filesz, "p_memsz": memsz,
                        "passed": passed})
    expected_payload = b"".join(bytes((tag, 0xa5)) for tag in (0x11, 0x22, 0x33)[:count])
    checks["program_headers"] = all(row["passed"] for row in headers)
    checks["payload"] = data[table_end:] == expected_payload
    return {"program_count": count, "e_phoff": phoff, "table_end": table_end,
            "checks": checks, "headers": headers, "passed": all(checks.values())}


def check_fixture(path, count):
    data = path.read_bytes()
    checked = check_bytes(data, count)
    if len(data) >= HEADER.size:
        # The original writer encoded 64 + 56 * phnum here. Feed that value
        # back through the same comparator; even phnum=0 must reject 64.
        mutated = bytearray(data)
        mutated[32:40] = struct.pack("<Q", HEADER.size + PROGRAM.size * count)
        checked["checks"]["old_phoff_mutation_rejected"] = not check_bytes(mutated, count)["passed"]
        checked["passed"] = all(checked["checks"].values())
    checked.update({"file": path.name, "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)})
    return checked


def readelf_check(path, count):
    header = command(["readelf", "-h", str(path)])
    segments = command(["readelf", "-lW", str(path)])
    expected_phoff = 0 if count == 0 else 64
    expected_start = f"Start of program headers:          {expected_phoff} (bytes into file)"
    expected_count = f"Number of program headers:         {count}"
    passed = (header["status"] == "completed" and header["exit"] == 0 and
              segments["status"] == "completed" and segments["exit"] == 0 and
              expected_start in header["stdout"] and expected_count in header["stdout"] and
              (count == 0 or segments["stdout"].count("LOAD") == count))
    return {"file": path.name, "passed": passed, "header": header, "segments": segments}


def main():
    if len(sys.argv) != 2:
        raise SystemExit("usage: elf_phoff.py EMITTED_DIRECTORY")
    output = Path(sys.argv[1])
    report_path = output / "elf-phoff-results.json"
    report = {"schema_version": 1,
              "scope": "independent serialized ELF target comparison; not execution or loadability validation",
              "python_version": sys.version,
              "probe_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "fixtures": [], "readelf": [], "harness_errors": []}
    readelf = shutil.which("readelf")
    if not readelf:
        report["harness_errors"].append("readelf is required but was not found")
    else:
        version = command([readelf, "--version"])
        report["readelf_version"] = version
        if version["status"] != "completed" or version["exit"] != 0:
            report["harness_errors"].append("readelf --version failed")
    for name, count in FIXTURES:
        path = output / name
        if not path.is_file():
            report["harness_errors"].append(f"missing fixture: {name}")
            continue
        try:
            report["fixtures"].append(check_fixture(path, count))
            if readelf:
                report["readelf"].append(readelf_check(path, count))
        except (OSError, struct.error) as error:
            report["harness_errors"].append(f"{name}: {type(error).__name__}: {error}")
    passed = (not report["harness_errors"] and len(report["fixtures"]) == len(FIXTURES) and
              all(row["passed"] for row in report["fixtures"]) and
              len(report["readelf"]) == len(FIXTURES) and all(row["passed"] for row in report["readelf"]))
    report["passed"] = passed
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
