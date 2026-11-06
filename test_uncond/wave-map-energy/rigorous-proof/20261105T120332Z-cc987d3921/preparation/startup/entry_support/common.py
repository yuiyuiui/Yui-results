"""Shared mechanical entry checks; no mathematical construction or model calls."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys


def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def local(root, relative):
    if not isinstance(relative,str) or not relative:raise ValueError('Use a nonempty entry-relative path')
    root=Path(root).resolve();part=Path(relative)
    if part.is_absolute() or '..' in part.parts or part==Path('.'):
        raise ValueError('Use a nonempty entry-relative path')
    path=root
    for item in part.parts:
        path=path/item
        if path.is_symlink():raise ValueError('Entry paths cannot follow symlinks')
    if not path.resolve().is_relative_to(root):raise ValueError('Path escaped its entry')
    return path


def write(path,value,*,exclusive=False):
    path=Path(path)
    if path.is_symlink():raise ValueError('Refuse metadata symlink')
    path.parent.mkdir(parents=True,exist_ok=True)
    text=json.dumps(value,ensure_ascii=False,indent=2)+'\n'
    if exclusive:
        with path.open('x') as stream:stream.write(text)
    else:
        import uuid
        scratch=path.with_name(path.name+'.'+uuid.uuid4().hex+'.tmp')
        try:scratch.write_text(text);scratch.replace(path)
        finally:scratch.unlink(missing_ok=True)


def json_call(command,*,data=None,timeout=180,log=None):
    try:
        result=subprocess.run([str(x) for x in command],input=None if data is None else json.dumps(data),
            capture_output=True,text=True,timeout=timeout)
    except subprocess.TimeoutExpired as error:
        if log:write(log,{'argv':[str(x) for x in command],'exit_code':None,'timeout_seconds':timeout,
            'stdout':str(error.stdout or ''),'stderr':str(error.stderr or '')})
        raise
    if log:write(log,{'argv':[str(x) for x in command],'exit_code':result.returncode,'stdout':result.stdout,'stderr':result.stderr})
    if result.returncode:raise ValueError('Command failed: '+(result.stderr or result.stdout)[-3000:])
    value=json.loads(result.stdout)
    if not isinstance(value,dict):raise ValueError('Expected a JSON object')
    return value


def runtime_call(runtime,program,*args,data=None,timeout=180,log=None):
    return json_call([sys.executable,'-B','-c',program,str(runtime),*args],data=data,timeout=timeout,log=log)


CAPABILITY_CHECK = '''import json,sys
from pathlib import Path
root=Path(sys.argv[1]);mode=sys.argv[2]
sys.path[:0]=[str(root/'nl0/scripts'),str(root/'nl02lean/scripts')]
supported=(root/'nl0/scripts/basis.py').is_file() and (root/'nl02lean/scripts/b2lean.py').is_file()
if mode=='unconditional':
 if not supported:raise ValueError('The registered Yui lacks unconditional formalization; select a capable installation before starting')
 import basis,b2lean
 basis.validate_mode(mode,'full')
 if not callable(getattr(b2lean,'validate_receipt',None)):raise ValueError('Missing final b2lean validation')
print(json.dumps({'unconditional_supported':supported,'formalization':mode}))
'''


TERMINAL_CHECK = '''import json,sys
from pathlib import Path
root=Path(sys.argv[1]);run=Path(sys.argv[2]).resolve();mode=sys.argv[3]
sys.path[:0]=[str(root/'nl0/scripts'),str(root/'nl02lean/scripts')]
from source_preparation import read_source
from final_acceptance import validate_receipt
result=json.loads((run/'case-result.json').read_text())['result']
value={'audit_a':'NOT_AVAILABLE','audit_b':'NOT_AVAILABLE','basis_closure':'NOT_AVAILABLE',
 'mathematics_automatically_verified':False,'formalization':mode}
source=run/'source-selection.json'
if source.is_file():
 data=read_source(**json.loads(source.read_text()))[0][0]
 value['audit_a']={k:data.get(k) for k in ('current_standard_receipt_valid','current_conditional_receipt_valid','source_warnings','unresolved_reviews')}
receipt=(result.get('audit_b') or {}).get('receipt_path')
if receipt:
 path=Path(receipt).resolve()
 if not path.is_relative_to(run):raise ValueError('Final receipt is outside this run')
 checked=validate_receipt(path)
 value['audit_b']={k:checked.get(k) for k in ('status','acceptance_basis','source_conditional','freeze_deviation','final_semantic_model_called')}
status=result['status']
if status=='DRAFT-AUDIT-PASSED' and (not isinstance(value['audit_a'],dict) or not value['audit_a'].get('current_standard_receipt_valid')):
 raise ValueError('Audit A PASS lacks actual authority')
if status in ('WORKFLOW-PASSED','WORKFLOW-CONDITIONAL') and not isinstance(value['audit_b'],dict):raise ValueError('Missing machine Audit B authority')
if status=='WORKFLOW-PASSED' and value['audit_b'].get('status')!='AUDIT-B-PASSED':raise ValueError('Workflow PASS lacks Audit B acceptance')
if mode=='unconditional':
 if result.get('formalization_goal')!='unconditional':raise ValueError('Unconditional goal was changed or omitted')
 if status in ('DRAFT-AUDIT-PASSED','DRAFT-AUDIT-CONDITIONAL','AUDIT-B-PASSED','AUDIT-B-CONDITIONAL'):
  raise ValueError('Intermediate acceptance cannot finish an unconditional full workflow')
 if status in ('WORKFLOW-PASSED','WORKFLOW-CONDITIONAL'):
  import b2lean
  closure=run/'b2lean'
  if closure.is_symlink():raise ValueError('Final closure cannot be a symlink')
  final=b2lean.validate_receipt(closure)
  if final['status']!=status or result.get('closure')!=final['closure']:raise ValueError('Final closure differs from delivered result')
  value['basis_closure']={k:final.get(k) for k in ('status','achieved_scope','closure','source_conditional')}
  if status=='WORKFLOW-PASSED' and (not final['closure'].get('unconditional') or final.get('achieved_scope')!='UNCONDITIONAL_LEAN'):
   raise ValueError('Conditional intermediate is not unconditional completion')
print(json.dumps(value))
'''


def terminal_check(runtime,workflow,mode):
    return runtime_call(runtime,TERMINAL_CHECK,str(workflow),mode)


def support_bindings():
    return {p.name:digest(p) for p in sorted(Path(__file__).parent.glob('*.py'))}


def terminal_ready(snapshot):
    if not isinstance(snapshot,dict):return False
    cases=snapshot.get('cases')
    if not isinstance(cases,list) or len(cases)!=1 or not isinstance(cases[0],dict):return False
    case=cases[0]
    if not isinstance(case.get('counts'),dict):return False
    return (snapshot.get('all_terminal') is True and snapshot.get('all_process_exits_verified') is True
        and snapshot.get('process_inspection_error') is None and case.get('terminal_record_present') is True
        and case.get('process_exit_verified') is True and case.get('phase')!='PAUSED_ERROR'
        and not (case.get('counts') or {}).get('PAUSED_ERROR') and case.get('paused_errors')==[]
        and type(case.get('live_owned_process_count')) is int and case['live_owned_process_count']==0
        and case.get('registered_groups_still_present')==[])
