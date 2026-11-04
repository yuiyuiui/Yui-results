#!/usr/bin/env python3
"""Rebuild the whole supplementary chain and inspect its signature."""
import hashlib, json, os, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parent
LEAN = "/Users/syyui/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean"
EXPECTED = "bf73ff25c1c67c020023ad545649bd2e0444658191c6c0c637b86528ad0b0cd0"
actual = hashlib.sha256((ROOT / "OriginalProof.lean").read_bytes()).hexdigest()
if actual != EXPECTED:
    sys.exit("OriginalProof.lean hash mismatch: " + actual)
status = {"original_sha256": actual, "modules": [], "build_only": True, "root_declaration": "BareModelCompletion.completed_theorem_1"}
for name in ["OriginalProof", "OriginalExternals", "GalerkinBridges", "ExternalBridges", "StageBridges", "PaddingHelpers", "FlowLimitHelpers", "RegularityBridges", "CompletedProof", "SignatureInspection"]:
    command = [LEAN, "-o", name + ".olean", name + ".lean"]
    with (ROOT / (name + "-build.log")).open("w") as log:
        proc = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    status["modules"].append({"module": name, "command": command, "exit_code": proc.returncode})
    (ROOT / "build-status.json").write_text(json.dumps(status, indent=2) + "\n")
    print(name + ": exit " + str(proc.returncode), flush=True)
    if proc.returncode:
        sys.exit(proc.returncode)
status["original_sha256_after"] = hashlib.sha256((ROOT / "OriginalProof.lean").read_bytes()).hexdigest()
(ROOT / "build-status.json").write_text(json.dumps(status, indent=2) + "\n")
