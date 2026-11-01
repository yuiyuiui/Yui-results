from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, re, shutil, subprocess, time

ROOT = Path(__file__).resolve().parent
SOURCE = Path('/Users/syyui/projects/Yui-results/benchmark/pure-model-result/20261028T154300Z-b21e5d9a/Proof.lean')
MATHLIB = Path('/Users/syyui/formalization-tools/lean-mathlib-v4.32.2/mathlib')
LEAN = Path('/Users/syyui/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean')
shutil.copyfile(SOURCE, ROOT/'Proof.lean')
paths = [ROOT, MATHLIB/'.lake/build/lib/lean']
paths += sorted((MATHLIB/'.lake/packages').glob('*/.lake/build/lib/lean'))
env = dict(os.environ, LEAN_PATH=':'.join(map(str,paths)))
names = ['TheoremOne','ExactSolution','LiWuStepIdentity','LiWuStageEstimate',
         'LiWuProductEstimate','LiWuTrilinearEstimate','BITGalerkinEstimate',
         'BITExistenceLimit','BITHigherRegularity','BITLowRegularity','BITWeakerLipschitz']
inspect = 'import Proof\nset_option pp.universes true\nset_option pp.explicit true\nset_option pp.proofs false\n#check @theorem_1\n#print axioms theorem_1\n'
inspect += ''.join('#print KdV.'+n+'\n' for n in names)
(ROOT/'Inspect.lean').write_text(inspect)
report = {'schema':'yui-direct-fidelity-mechanical-audit-1',
          'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
          'lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),
          'mathlib_commit':subprocess.check_output(['git','-C',str(MATHLIB),'rev-parse','HEAD'],text=True).strip(),
          'scope':'Fresh temporary copy; existing run, source, logs and compiled artifacts are not modified.',
          'commands':[]}
text=SOURCE.read_text()
report['forbidden_token_scan']={x:len(re.findall(r'\b'+x+r'\b',text)) for x in ['sorry','admit','axiom','opaque','unsafe']}
for args,log in [(['Proof.lean','-o','Proof.olean'],'clean-build.log'),(['Inspect.lean'],'signature-inspection.log')]:
    started=datetime.now(timezone.utc).isoformat();begin=time.monotonic()
    with (ROOT/log).open('w') as f:
        result=subprocess.run([str(LEAN),*args],cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
    entry={'args':args,'started_at_utc':started,'finished_at_utc':datetime.now(timezone.utc).isoformat(),
           'elapsed_seconds':time.monotonic()-begin,'exit_code':result.returncode,'log':str(ROOT/log)}
    report['commands'].append(entry)
    (ROOT/'mechanical-audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(entry),flush=True)
    if result.returncode:
        print((ROOT/log).read_text()[-6000:],flush=True)
        raise SystemExit(result.returncode)
report['original_source_unchanged']=hashlib.sha256(SOURCE.read_bytes()).hexdigest()==report['source_sha256']
(ROOT/'mechanical-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'MECHANICAL_CHECKS_PASSED','report':str(ROOT/'mechanical-audit.json')}),flush=True)
