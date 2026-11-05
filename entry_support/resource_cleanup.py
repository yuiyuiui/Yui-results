"""Remove only disposable resources of an explicitly terminal Yui run."""
from pathlib import Path
import importlib
import json
import os
import shutil
import signal
import sys
import time


def stage_retains_workspace(stage,workspace):
    result=json.loads(stage.read_text())
    retention=result.get('workspace_retention',{})
    if not isinstance(retention,dict):
        raise ValueError('Invalid workspace retention record: '+str(stage))
    if not retention:return False
    recorded=retention.get('workspace')
    if not isinstance(recorded,str) or not os.path.isabs(recorded):
        raise ValueError('Expected an absolute retained workspace path: '+str(stage))
    try:
        return os.path.samefile(workspace,recorded)
    except FileNotFoundError as error:
        if error.filename!=recorded:raise
        # A stage record can outlive its workspace. Only a confirmed release
        # allows other owned scratch to be cleaned when that path is missing.
        if result.get('temporary_workspace_removed') is True:return False
        if result.get('temporary_workspace_removed') is False:
            from run_resources import safe_stage_workspace
            if safe_stage_workspace(result):return False
        raise ValueError('Cannot verify release of missing retained workspace: '+recorded) from error


def clean_workflow(workflow,runtime,*,grace=2):
    if any(p.is_symlink() for raw in (workflow,runtime) for p in [Path(raw),*Path(raw).parents]):
        raise ValueError('Cleanup cannot follow a symlink workflow or runtime')
    workflow=Path(workflow).resolve();runtime=Path(runtime).resolve()
    if not 0<=grace<=30:raise ValueError('Cleanup grace must be between 0 and 30 seconds')
    if not (workflow/'case-result.json').is_file():raise ValueError('No terminal case result; keep active resources')
    result=json.loads((workflow/'case-result.json').read_text())
    if result.get('result',{}).get('status') not in {'WORKFLOW-PASSED','WORKFLOW-CONDITIONAL','DRAFT-AUDIT-PASSED',
            'DRAFT-AUDIT-CONDITIONAL','AUDIT-B-PASSED','AUDIT-B-CONDITIONAL','CANCELLED','STOPPED_BY_USER','DIFFERENT_RESULT_DELIVERED'}:
        raise ValueError('Unfinished/faulted workflow cannot authorize cleanup')
    sys.path[:0]=[str(runtime/'nl0/scripts'),str(runtime/'nl02lean/scripts')]
    owned=importlib.import_module('cleanup');faults=importlib.import_module('fault_control')
    if faults.pending(workflow):raise ValueError('A retained paused incident still needs a user decision')
    if result.get('job')!={'path':str(workflow/'job.json'),'sha256':__import__('hashlib').sha256((workflow/'job.json').read_bytes()).hexdigest()}:
        raise ValueError('Terminal result is not bound to this job')
    removed=[];stopped=[]
    with owned.cleanup_lock(workflow):
        inv=owned.inventory(owned.CORE,outputs=[workflow])
        if inv['errors']:raise ValueError('Unconfirmed resource ownership: '+str(inv['errors']))
        # A retained native workspace can itself support an accepted stage's
        # health record. Only the runtime may release that binding; do not
        # erase it and invalidate the proof evidence during garbage collection.
        for path,record in inv['workspaces'].items():
            info=json.loads(Path(record).read_text());stage=Path(info['logs'])/'result.json'
            if stage.is_file() and stage_retains_workspace(stage,path):
                raise ValueError('Runtime must release the evidence-bound native workspace first: '+str(path))
        live=owned.discover(inv,owned.process_table(),owned.CORE)
        if inv['errors']:raise ValueError('Unconfirmed process ownership: '+str(inv['errors']))
        if os.getpid() in live:raise ValueError('Cleanup cannot stop its own caller')
        stopped=list(live)
        owned.signal_owned(live,signal.SIGTERM)
        deadline=time.monotonic()+grace
        while live and time.monotonic()<deadline:
            time.sleep(.05);inv=owned.inventory(owned.CORE,outputs=[workflow])
            live=owned.discover(inv,owned.process_table(),owned.CORE)
        if inv['errors']:raise ValueError('Resource ownership became uncertain')
        owned.signal_owned(live,signal.SIGKILL)
        deadline=time.monotonic()+3
        while live and time.monotonic()<deadline:
            time.sleep(.05);inv=owned.inventory(owned.CORE,outputs=[workflow])
            live=owned.discover(inv,owned.process_table(),owned.CORE)
        if live or inv['errors']:raise ValueError('Owned process exit is not confirmed; preserve files')
        for path in inv['workspaces']:
            shutil.rmtree(path);removed.append(str(path))
        candidates=[];caches=[]
        for directory,dirs,files in os.walk(workflow,followlinks=False):
            base=Path(directory)
            dirs[:]=[d for d in dirs if not (base/d).is_symlink() and d not in {'runtime','inputs'}]
            for name in list(dirs):
                if name in {'__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'}:
                    caches.append(base/name);dirs.remove(name)
            for name in files:
                path=base/name
                if not path.is_symlink() and (path.suffix in {'.olean','.ilean','.pyc','.pyo','.tmp'} or name=='.DS_Store'):
                    candidates.append(path)
        # Native binary/helper evidence referenced by a record is useful, not
        # garbage. Preserve it even when it can be rebuilt from Lean source.
        mentioned=set()
        cache_files=[p for cache in caches for p in cache.rglob('*') if p.is_file() and not p.is_symlink()]
        if candidates or cache_files:
            needles={p.name for p in candidates+cache_files}
            for path in workflow.rglob('*.json'):
                if path.is_symlink():continue
                raw=path.read_text(errors='replace')
                mentioned.update(name for name in needles-mentioned if name in raw)
        for path in candidates:
            if path.name not in mentioned:path.unlink();removed.append(str(path))
        for path in caches:
            if not any(p.name in mentioned for p in cache_files if p.is_relative_to(path)):
                shutil.rmtree(path);removed.append(str(path))
    return {'status':'CLEANED','residual_owned_processes':[],'stopped_processes':stopped,
        'removed':removed,'scope':'Only this terminal run: marked scratch, unbound compiled files and disposable caches. Inputs, proofs, records, runtime and shared toolchains retained.'}


if __name__=='__main__':
    try:
        value=clean_workflow(sys.argv[1],sys.argv[2])
        print(json.dumps(value))
    except (OSError,ValueError,KeyError) as error:
        print(json.dumps({'status':'CLEANUP_BLOCKED','error':str(error)}));raise SystemExit(1)
