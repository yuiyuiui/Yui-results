#!/usr/bin/env python3
"""Reproduce the completed review-002 build without changing mathematical sources."""
from pathlib import Path
import hashlib, json, os, subprocess, datetime
O=Path(__file__).resolve().parent
W=O.parent/'review-002-work'
LEAN='/Users/syyui/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean'
EXPECTED='bf73ff25c1c67c020023ad545649bd2e0444658191c6c0c637b86528ad0b0cd0'
mods=['OriginalProof','OriginalExternals','GalerkinBridges','ExternalBridges','StageBridges','PaddingHelpers','FlowLimitHelpers','RegularityBridges','SolutionCorrespondence','CompletedProof','SignatureInspection']
assert hashlib.sha256((W/'OriginalProof.lean').read_bytes()).hexdigest()==EXPECTED
status={'lean':LEAN,'cwd':str(W),'LEAN_PATH':os.environ['LEAN_PATH'],'original_sha256_before':EXPECTED,'modules':[]}
for name in mods:
    cmd=[LEAN,'-o',str(W/(name+'.olean')),str(W/(name+'.lean'))]
    started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    with (O/(name+'-build.log')).open('w') as log:
        proc=subprocess.run(cmd,cwd=W,stdout=log,stderr=subprocess.STDOUT)
    status['modules'].append({'module':name,'command':cmd,'started':started,'exit_code':proc.returncode,'log':str(O/(name+'-build.log'))})
    (O/'review-build-status.json').write_text(json.dumps(status,indent=2))
    print(name,proc.returncode,flush=True)
status['original_sha256_after']=hashlib.sha256((W/'OriginalProof.lean').read_bytes()).hexdigest()
assert status['original_sha256_after']==EXPECTED
(O/'review-build-status.json').write_text(json.dumps(status,indent=2))
