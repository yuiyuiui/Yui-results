#!/usr/bin/env python3
"""Review-only rebuild; preserves candidate sources and writes complete logs here."""
import datetime, hashlib, json, os, pathlib, subprocess
OUT = pathlib.Path(__file__).resolve().parent
ROOT = OUT.parent / "review-001-work"
LEAN = "/Users/syyui/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean"
EXPECTED = "bf73ff25c1c67c020023ad545649bd2e0444658191c6c0c637b86528ad0b0cd0"
MODS = ["OriginalProof", "OriginalExternals", "GalerkinBridges", "ExternalBridges", "StageBridges", "PaddingHelpers", "FlowLimitHelpers", "RegularityBridges", "CompletedProof", "SignatureInspection"]
assert hashlib.sha256((ROOT / "OriginalProof.lean").read_bytes()).hexdigest() == EXPECTED
status = {"lean": LEAN, "cwd": str(ROOT), "LEAN_PATH": os.environ["LEAN_PATH"], "original_sha256_before": EXPECTED, "modules": []}
for name in MODS:
    command = [LEAN, "-o", str(ROOT / (name + ".olean")), str(ROOT / (name + ".lean"))]
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with (OUT / (name + "-build.log")).open("w") as log:
        proc = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    status["modules"].append({"module": name, "command": command, "started": started, "exit_code": proc.returncode, "log": str(OUT / (name + "-build.log"))})
    (OUT / "review-build-status.json").write_text(json.dumps(status, indent=2))
    print(name, proc.returncode, flush=True)
status["original_sha256_after"] = hashlib.sha256((ROOT / "OriginalProof.lean").read_bytes()).hexdigest()
assert status["original_sha256_after"] == EXPECTED
(OUT / "review-build-status.json").write_text(json.dumps(status, indent=2))
