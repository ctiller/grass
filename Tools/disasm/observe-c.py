"""Native corroboration only: observe the controlled C store in a child process.

The 8-byte target and adjacent 8-byte canary share one allocated structure. This
lets the bad fixture cross the target's boundary without targeting unrelated
process memory. No runtime observation here is promoted to a Lean proof.
"""
import argparse
import ctypes
import hashlib
import json
import os
import pathlib
import subprocess
import sys


class Frame(ctypes.Structure):
    _fields_ = [("target", ctypes.c_uint32 * 2), ("canary", ctypes.c_uint32 * 2)]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def observe(directory, case):
    library = (directory / (case + ".dll")).resolve()
    manifest_path = (directory / "manifest.json").resolve()
    manifest = json.loads(manifest_path.read_text(encoding="utf-8-sig"))
    records = [record for record in manifest.get("fixtures", []) if record.get("case") == case]
    require(len(records) == 1, "manifest must contain exactly one record for " + case)
    record = records[0]
    require(record.get("library") == library.name, "manifest DLL name mismatch for " + case)
    before_hash = sha256(library)
    require(before_hash.lower() == record.get("librarySha256", "").lower(),
            "DLL hash does not match build manifest for " + case)
    loaded = ctypes.CDLL(str(library))
    function = loaded.probe
    function.argtypes = [ctypes.POINTER(ctypes.c_uint32)]
    function.restype = None
    frame = Frame((10, 11), (0xFEEDBEEF, 0xABCDABCD))
    require(ctypes.sizeof(Frame) == 16 and Frame.canary.offset == 8,
            "unexpected Frame layout; refusing native call")
    before = {"target": list(frame.target), "canary": list(frame.canary)}
    function(frame.target)
    after = {"target": list(frame.target), "canary": list(frame.canary)}
    after_hash = sha256(library)
    require(after_hash == before_hash, "DLL changed while native observation was running")
    return {"case": case, "binary": library.name,
            "sha256": before_hash,
            "targetSize": ctypes.sizeof(frame.target), "allocationSize": ctypes.sizeof(frame),
            "before": before, "after": after,
            "adjacentObjectChanged": before["canary"] != after["canary"]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("directory", type=pathlib.Path)
    parser.add_argument("--case", choices=["store_safe", "store_oob", "sequence_safe", "sequence_oob"])
    parser.add_argument("--family", choices=["store", "sequence"], default="store")
    options = parser.parse_args()
    if os.name != "nt" or ctypes.sizeof(ctypes.c_void_p) != 8:
        parser.error("this native corroboration harness requires 64-bit Windows Python")
    if options.case:
        print(json.dumps(observe(options.directory, options.case)))
        return
    results = []
    for case in (options.family + "_safe", options.family + "_oob"):
        child = subprocess.run([sys.executable, __file__, str(options.directory), "--case", case],
                               capture_output=True, text=True, timeout=15, check=True)
        results.append(json.loads(child.stdout))
    first = 11 if options.family == "sequence" else 10
    require(results[0]["after"]["target"] == [first, 42], "safe target result mismatch")
    require(not results[0]["adjacentObjectChanged"], "safe case changed adjacent object")
    require(results[1]["after"]["target"] == [first, 11], "OOB target result mismatch")
    require(results[1]["after"]["canary"] == [42, 0xABCDABCD],
            "OOB canary result mismatch")
    print(json.dumps({"schema": "grass.disasm.native-observation.v1",
                      "assurance": "runtime corroboration only; not a proof certificate",
                      "results": results}, indent=2))


if __name__ == "__main__":
    main()
