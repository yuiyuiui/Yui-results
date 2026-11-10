#!/usr/bin/env python3
"""Yui-benchmark preparation and guarded calls to the existing Yui runtime.

README.md is the operator entry. This adapter creates no task prompts, proof
strategy, repair loop, peer task or scheduler. Only `launch` starts model work.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from resource_cleanup import TERMINAL_OUTCOMES
import uuid

from benchmark_config import ROOT, load_config, local_path
from skill_check import require_skill
from owner_monitor import record_monitor

STARTUP_FILES = ('AGENTS.md', 'README.md', 'settings.json', 'benchmark_config.py',
                 'skill_check.py', 'prepare_yui.py', 'resource_cleanup.py', 'owner_monitor.py')
RECORD = 'BENCHMARK_RUN.json'
SCHEMA = 'yui-benchmark-run-1'


class RunFailure(ValueError):
    def __init__(self, run, error):
        self.run = str(run)
        super().__init__(type(error).__name__+': '+str(error)+'; retained run: '+str(run))


def utc():
    return datetime.now(timezone.utc).isoformat()


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    value = json.loads(Path(path).read_text())
    if not isinstance(value, dict):
        raise ValueError('Expected a JSON object: '+str(path))
    return value


def write(path, value, *, exclusive=False):
    path = Path(path)
    if path.is_symlink():
        raise ValueError('Do not write through a symlink: '+str(path))
    text = json.dumps(value, indent=2, ensure_ascii=False)+'\n'
    if exclusive:
        with path.open('x') as out:
            out.write(text)
    else:
        scratch = path.with_name(path.name+'.'+uuid.uuid4().hex+'.tmp')
        try:
            with scratch.open('x') as out:
                out.write(text)
            os.replace(scratch, path)
        finally:
            scratch.unlink(missing_ok=True)


def runtime_binding(installed):
    root = Path(installed['root'])
    rows = {}
    for name in ('SKILL.md', 'config.json', 'nl0', 'nl02lean', 'toolchain'):
        start = root / name
        paths = [start] if start.is_file() else start.rglob('*')
        for path in paths:
            if '__pycache__' in path.parts or 'tests' in path.relative_to(root).parts:
                continue
            if path.is_file() and path.suffix in {'.py', '.md', '.json', '.mjs', '.lean'}:
                rows[str(path.relative_to(root))] = sha256(path)
    def git(*args):
        result = subprocess.run(['git', '-C', str(root), *args], capture_output=True,
                                text=True, check=False)
        return result.stdout.strip() if result.returncode == 0 else None
    status = git('status', '--porcelain')
    return {'sha256': hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest(),
            'files': len(rows), 'source_commit': git('rev-parse', 'HEAD'),
            'branch': git('branch', '--show-current'),
            'dirty': None if status is None else bool(status)}


def bindings(installed, config):
    value = {'startup': {name: sha256(ROOT / name) for name in STARTUP_FILES},
             'paper_sha256': sha256(local_path(config['paper'])),
             'installed': {k: installed[k] for k in ('name', 'skill_md', 'root', 'skill_sha256')},
             'runtime': runtime_binding(installed)}
    if value['paper_sha256'] != config['paper_sha256']:
        raise ValueError('Original benchmark PDF hash mismatch')
    for key, actual in [('expected_commit', value['runtime']['source_commit']),
                        ('expected_sha256', value['runtime']['sha256'])]:
        expected = config['runtime'][key]
        if expected is not None and actual != expected:
            raise ValueError('Installed Yui runtime differs from '+key)
    return value


def json_process(command, *, data=None, timeout=60, log=None):
    try:
        result = subprocess.run([str(x) for x in command],
                                input=json.dumps(data) if data is not None else None,
                                capture_output=True, text=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired as error:
        if log is not None:
            def decoded(value):
                return value.decode(errors='replace') if isinstance(value, bytes) else value
            write(log, {'argv': [str(x) for x in command], 'exit_code': None,
                        'timeout_seconds': timeout, 'stdout': decoded(error.stdout),
                        'stderr': decoded(error.stderr), 'recorded_at_utc': utc()})
        raise
    if log is not None:
        write(log, {'argv': [str(x) for x in command], 'exit_code': result.returncode,
                    'stdout': result.stdout, 'stderr': result.stderr, 'recorded_at_utc': utc()})
    if result.returncode:
        raise ValueError('Command failed (exit '+str(result.returncode)+'): '+
                         (result.stderr or result.stdout)[-2500:])
    try:
        value = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise ValueError('Command returned malformed JSON: '+result.stdout[-500:]) from error
    if not isinstance(value, dict):
        raise ValueError('Command must return a JSON object')
    return value


def runtime_program(installed, program, *args, data=None, timeout=60):
    return json_process([sys.executable, '-B', '-c', program, installed['root'], *args],
                        data=data, timeout=timeout)


def environment_check(installed, config):
    program = '''import json,sys,shutil,importlib.util
from pathlib import Path
root=Path(sys.argv[1]);config=json.load(sys.stdin)
sys.path[:0]=[str(root/'nl0/scripts'),str(root/'nl02lean/scripts')]
from runtime_config import verify,auth_home,native_timeout
from entrypoint import preflight_profiles
preflight_profiles({'track':config['track'],'profiles':config['profiles']})
mode=config['formalization']
supported=(root/'nl0/scripts/basis.py').is_file() and (root/'nl02lean/scripts/b2lean.py').is_file()
if mode=='unconditional':
 if not supported:raise ValueError('The registered Yui has no unconditional formalization support')
 import basis,b2lean
 basis.validate_mode(mode,config['track'])
 if not callable(getattr(b2lean,'validate_receipt',None)):raise ValueError('Missing b2lean validator')

if not (auth_home()/'auth.json').is_file():raise ValueError('Codex authentication file is absent')
runtime=json.loads((root/'config.json').read_text())
if runtime['timeouts']!={k:config['limits'][k] for k in ('case_seconds','stage_seconds','native_seconds')} or runtime['token_budget'] is not None:
 raise ValueError('Installed timeout/token policy differs from this benchmark')
if native_timeout()!=config['limits']['native_seconds']:raise ValueError('Native-call limit differs')
environment=verify()
missing=[name for name in ('pdfinfo','pdftoppm') if not shutil.which(name)]
if missing:raise ValueError('Full-paper preparation needs Poppler tools on PATH: '+', '.join(missing))
if not shutil.which('pdftotext') and importlib.util.find_spec('pypdf') is None:
 raise ValueError('PDF extraction needs pdftotext or pypdf in the selected Python environment')
print(json.dumps({'status':'ENVIRONMENT-CHECKED','resolved_environment':environment,
 'pdf_tools':{name:shutil.which(name) for name in ('pdftotext','pdfinfo','pdftoppm')},
 'pdf_text_method':'pdftotext-layout' if shutil.which('pdftotext') else 'pypdf-text',
 'profile_metadata_verified':True,'authentication_file_present':True,'unconditional_supported':supported,
 'model_started':False,'proof_check_started':False,'actual_service_tier':None,
 'provider_quota_verified':False}))
'''
    return runtime_program(installed, program, data=config)


def checked_environment(codex=None):
    config = load_config()
    if sha256(local_path(config['paper'])) != config['paper_sha256']:
        raise ValueError('Original benchmark PDF hash mismatch')
    installed = require_skill(codex=codex, skill_name=config['skill_name'])
    bound = bindings(installed, config)
    environment = environment_check(installed, config)
    return config, installed, bound, environment


def run_path(value):
    base = local_path('results')
    path = Path(value).expanduser().absolute()
    if '..' in path.parts or path.parent.resolve() != base.resolve() or path.is_symlink() or not path.is_dir():
        raise ValueError('Select one direct, owned results/<run-id> directory without symlinks')
    return path.resolve()


def owned_file(run, relative):
    return local_path(relative, root=run)


def load_run(value):
    run = run_path(value)
    record = read(owned_file(run, RECORD))
    if record.get('schema') != SCHEMA or record.get('run') != str(run):
        raise ValueError('Missing or relocated run ownership record; historical runs are read-only evidence')
    return run, record


def update(run, record, status, **extra):
    record.update(status=status, updated_at_utc=utc(), **extra)
    write(run / RECORD, record)
    return record


def fail(run, record, status, error):
    update(run, record, status, failure={'type': type(error).__name__, 'detail': str(error),
                                       'recorded_at_utc': utc(), 'automatic_retry': False})


def extract_source(pdf, prep, config, tools, installed):
    program = '''import json,sys
from pathlib import Path
root=Path(sys.argv[1]);sys.path.insert(0,str(root/'nl0/scripts'))
from target_selection import text
print(json.dumps({'text':text(Path(sys.argv[2]))}))
'''
    # Use Yui's own ordered extractor, including its existing pypdf fallback.
    extracted = runtime_program(installed, program, str(pdf))['text']
    if not isinstance(extracted, str) or not extracted.strip():
        raise ValueError('PDF extraction failed or empty')
    info = subprocess.run([tools['pdfinfo'], str(pdf)], capture_output=True, text=True,
                          env=dict(os.environ, LC_ALL='C'), timeout=30, check=False)
    pages = re.search(r'^Pages:\s*(\d+)\s*$', info.stdout, re.MULTILINE)
    if info.returncode or not pages or int(pages.group(1)) < 1:
        raise ValueError('Cannot determine the complete PDF page count')
    page_count = int(pages.group(1))
    (prep / 'extracted.md').write_text(extracted)
    (prep / 'checked-source.md').write_text(extracted)
    (prep / 'target-statement.md').write_text('')
    images = prep / 'pages'; images.mkdir()
    rendered = subprocess.run([tools['pdftoppm'], '-r', str(config['preparation']['render_dpi']),
                               '-png', str(pdf), str(images / 'page')],
                              capture_output=True, text=True, timeout=180, check=False)
    files = sorted(images.glob('page-*.png'))
    numbers = {int(p.stem.split('-')[-1]) for p in files}
    if rendered.returncode or len(files) != page_count or numbers != set(range(1, page_count+1)) or any(not p.stat().st_size for p in files):
        raise ValueError('Full-paper rendering failed: '+rendered.stderr[-1500:])
    exports = {str(p.relative_to(prep)): sha256(p) for p in [pdf, prep/'extracted.md', *files]}
    return page_count, exports


def begin(*, codex=None, run_id=None):
    started = utc()
    config, installed, bound, environment = checked_environment(codex)
    run_id = run_id or datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:10]
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]{0,99}', run_id) or run_id in {'.', '..'}:
        raise ValueError('Use a simple fresh run ID, not a path')
    base = local_path(config['results_directory']); base.mkdir(exist_ok=True)
    run = local_path(config['results_directory']+'/'+run_id)
    run.mkdir(exist_ok=False)
    record = {'schema': SCHEMA, 'run': str(run.resolve()), 'status': 'PREPARING_SOURCE',
              'started_at_utc': started, 'configuration': config, 'bindings': bound,
              'installed': installed, 'environment': environment, 'model_started': False,
              'workflow': str(run/'workflow'), 'failure': None}
    try:
        write(run/RECORD, record, exclusive=True)
        prep = run/'preparation'; prep.mkdir()
        startup = prep/'startup'; startup.mkdir()
        for name in STARTUP_FILES:
            shutil.copyfile(ROOT/name, startup/name)
        pdf = prep/'original.pdf'; shutil.copyfile(local_path(config['paper']), pdf)
        count, exports = extract_source(pdf, prep, config, environment['pdf_tools'], installed)
        write(prep/'source-review.json', {'schema': 'yui-source-readback-1',
              'source_sha256': config['paper_sha256'], 'checked_pages': [],
              'transcription_checked': False, 'target_checked': False, 'source_only': False,
              'corrections': [], 'notes': ''}, exclusive=True)
        update(run, record, 'SOURCE_REVIEW_REQUIRED', page_count=count, source_exports=exports,
               source_readback_ready_at_utc=utc())
    except Exception as error:
        fail(run, record, 'PREPARATION_FAILED', error)
        raise RunFailure(run, error) from error
    return {'status': record['status'], 'run': str(run), 'preparation': str(prep),
            'page_count': count, 'model_started': False}


def verify_current(record, *, codex=None):
    config, installed, bound, environment = checked_environment(codex)
    if config != record['configuration'] or bound != record['bindings'] or environment_identity(environment) != environment_identity(record['environment']):
        raise ValueError('Preparation is stale: source, settings, entry, tools or registered Yui runtime changed')
    return installed


def environment_identity(value):
    # Yui's verifier timestamps each observation. Keep that in evidence while
    # comparing the actual tools/pins/profile availability, not the clock read.
    result = dict(value)
    resolved = dict(result['resolved_environment'])
    resolved.pop('observed_at_utc', None)
    result['resolved_environment'] = resolved
    return result


def verify_source(run, record, *, frozen=False):
    prep = owned_file(run, 'preparation')
    allowed = {'original.pdf', 'extracted.md', 'pages', 'startup', 'checked-source.md',
               'target-statement.md', 'source-review.json', 'target-selection.json'}
    if any(path.name not in allowed for path in prep.iterdir()):
        raise ValueError('Unexpected source-preparation file; do not add old results or extra briefing material')
    expected_pages = {name for name in record['source_exports'] if name.startswith('pages/')}
    actual_pages = {str(path.relative_to(prep)) for path in local_path('pages', root=prep).iterdir()}
    if actual_pages != expected_pages:
        raise ValueError('Source page inventory changed')
    if {path.name for path in local_path('startup', root=prep).iterdir()} != set(STARTUP_FILES):
        raise ValueError('Startup provenance inventory changed')
    for name, digest in record['bindings']['startup'].items():
        if sha256(local_path('startup/'+name, root=prep)) != digest:
            raise ValueError('Startup provenance changed: '+name)
    for relative, digest in record['source_exports'].items():
        if sha256(local_path(relative, root=prep)) != digest:
            raise ValueError('Original PDF, extraction or rendered page changed: '+relative)
    if frozen:
        for relative, digest in record['reviewed_inputs'].items():
            if sha256(local_path(relative, root=prep)) != digest:
                raise ValueError('Frozen reviewed input changed: '+relative)


def freeze(value, *, codex=None):
    run, record = load_run(value)
    if record['status'] != 'SOURCE_REVIEW_REQUIRED':
        raise ValueError('Freeze only this run\'s unsubmitted source review')
    installed = verify_current(record, codex=codex)
    verify_source(run, record)
    prep = owned_file(run, 'preparation')
    review = read(local_path('source-review.json', root=prep))
    if set(review) != {'schema', 'source_sha256', 'checked_pages', 'transcription_checked',
                       'target_checked', 'source_only', 'corrections', 'notes'}:
        raise ValueError('Use the complete source-review fields documented in README')
    if review['schema'] != 'yui-source-readback-1' or review['source_sha256'] != record['configuration']['paper_sha256']:
        raise ValueError('Source review belongs to another original')
    pages = review['checked_pages']
    if not isinstance(pages, list) or any(type(x) is not int for x in pages) or sorted(pages) != list(range(1, record['page_count']+1)):
        raise ValueError('Check every PDF page exactly once, including definitions, proof and references')
    if any(review[key] is not True for key in ('transcription_checked', 'target_checked', 'source_only')):
        raise ValueError('Complete the actual source-only transcription and target readback first')
    if not isinstance(review['notes'], str) or not isinstance(review['corrections'], list):
        raise ValueError('Source review notes/corrections have invalid types')
    for correction in review['corrections']:
        if not isinstance(correction, dict) or set(correction) != {'page', 'detail'} or type(correction['page']) is not int or correction['page'] not in pages or not isinstance(correction['detail'], str) or not correction['detail'].strip():
            raise ValueError('Every correction needs a checked page and concrete detail')
    for name in ('checked-source.md', 'target-statement.md'):
        if not local_path(name, root=prep).read_text().strip():
            raise ValueError('Complete the source-only file: '+name)
    program = '''import json,sys
from pathlib import Path
root=Path(sys.argv[1]);prep=Path(sys.argv[2]);sys.path.insert(0,str(root/'nl0/scripts'))
from target_selection import select
statement=(prep/'target-statement.md').read_text()
print(json.dumps(select(prep/'original.pdf',[{'id':'theorem-1','label':'Theorem 1',
 'statement':statement,'start_line':None}],basis='this_run_full_paper_readback')))
'''
    selection = runtime_program(installed, program, str(prep))
    if selection.get('document') != {'path': str(prep/'original.pdf'), 'sha256': record['configuration']['paper_sha256']}:
        raise ValueError('Target resolver did not bind this run\'s original PDF')
    write(prep/'target-selection.json', selection, exclusive=True)
    hashes = {name: sha256(local_path(name, root=prep)) for name in
              ('checked-source.md', 'target-statement.md', 'source-review.json', 'target-selection.json')}
    update(run, record, 'INPUTS_FROZEN', reviewed_inputs=hashes, inputs_frozen_at_utc=utc())
    return {'status': record['status'], 'run': str(run), 'model_started': False}


def validate_job(run, record):
    workflow = owned_file(run, 'workflow')
    job = read(local_path('job.json', root=workflow))
    config = record['configuration']; prep = run/'preparation'
    profiles = config['profiles'] if config['track'] == 'full' else dict(nl0=config['profiles']['nl0'], lean=config['profiles']['nl0'])
    expected = {'root': str(workflow), 'problem': str(prep/'original.pdf'),
                'track': config['track'], 'policy': config['policy'],
                'profiles': profiles, 'max_concurrency': config.get('workers', 'auto'),
                'source': None, 'audit': None, 'time_budget_seconds': None}
    mismatches = [key for key, value in expected.items() if job.get(key) != value]
    if job.get('formalization','conditional') != config['formalization']:mismatches.append('formalization')
    if mismatches:
        raise ValueError('Prepared Yui job differs from the configured benchmark: '+', '.join(mismatches))
    if 'resume' in job or job.get('target_selection') != read(prep/'target-selection.json'):
        raise ValueError('Do not import another run\'s authority or target')
    expected_documents = {'problem.md': prep/'original.pdf', 'material-001.md': prep/'checked-source.md',
                          'target-selection.json': prep/'original.pdf'}
    documents = job.get('documents')
    if not isinstance(documents, list) or len(documents) != len(expected_documents):
        raise ValueError('Unexpected inputs in prepared job')
    seen = set()
    for document in documents:
        name = document.get('id'); original = document.get('original', {})
        if name not in expected_documents or name in seen or document.get('path') != name:
            raise ValueError('Unexpected or duplicate job input')
        seen.add(name)
        source = expected_documents[name]
        if original != {'path': str(source), 'sha256': sha256(source)}:
            raise ValueError('Job input did not originate in this run: '+name)
        if sha256(local_path('inputs/'+name, root=workflow)) != document.get('sha256'):
            raise ValueError('Frozen job input changed: '+name)
    if (workflow/'inputs/material-001.md').read_bytes() != (prep/'checked-source.md').read_bytes():
        raise ValueError('Yui did not copy the checked source exactly')
    if read(workflow/'inputs/target-selection.json') != read(prep/'target-selection.json'):
        raise ValueError('Yui target differs from this run\'s reviewed target')
    return job


def prepare(value, *, codex=None):
    run, record = load_run(value)
    if record['status'] != 'INPUTS_FROZEN':
        raise ValueError('Prepare only after this run\'s reviewed inputs are frozen')
    installed = verify_current(record, codex=codex); verify_source(run, record, frozen=True)
    config = record['configuration']; prep = run/'preparation'
    if (run/'workflow').exists() or (run/'workflow').is_symlink():
        raise ValueError('Never overwrite or reuse a workflow directory')
    command = [sys.executable, '-B', str(Path(installed['root'])/'nl0/scripts/yui.py'),
               'prepare', str(prep/'original.pdf'), '--track', config['track'],
               '--policy', config['policy'],
               '--material', str(prep/'checked-source.md'), '--target-file', str(prep/'target-selection.json'),
               '--output', str(run/'workflow')]
    if 'workers' in config:
        command.extend(['--max-concurrency', str(config['workers'])])
    if config['formalization']=='unconditional' or record['environment'].get('unconditional_supported'):
        command += ['--formalization',config['formalization']]
    for phase in ('nl0', 'lean'):
        for flag, key in [('model', 'id'), ('effort', 'reasoning_effort'), ('speed', 'speed')]:
            command += ['--'+phase+'-'+flag, config['profiles'][phase][key]]
    write(run/'prepare-attempt.json', {'argv': command, 'started_at_utc': utc()}, exclusive=True)
    update(run, record, 'PREPARING_JOB')
    try:
        value = json_process(command, timeout=180, log=run/'prepare-result.json')
        if value.get('status') != 'PREPARED_NOT_STARTED' or value.get('runs') != [str(run/'workflow')]:
            raise ValueError('Yui prepare returned an unexpected result')
        validate_job(run, record)
        frozen = runtime_binding({'root': str(run/'workflow/runtime')})
        update(run, record, 'JOB_PREPARED', job_sha256=sha256(run/'workflow/job.json'),
               frozen_runtime_sha256=frozen['sha256'], job_prepared_at_utc=utc())
    except Exception as error:
        fail(run, record, 'JOB_PREPARATION_FAILED', error)
        raise
    return {'status': record['status'], 'run': str(run), 'workflow': str(run/'workflow'), 'model_started': False}


def frozen_entry(run):
    record = read(owned_file(run, RECORD))
    if runtime_binding({'root': str(owned_file(run, 'workflow/runtime'))})['sha256'] != record.get('frozen_runtime_sha256'):
        raise ValueError('This job\'s frozen runtime changed')
    entry = owned_file(run, 'workflow/runtime/nl0/scripts/yui.py')
    if not entry.is_file():
        raise ValueError('Missing this job\'s bound Yui runtime')
    return entry


def launch(value, *, codex=None, heartbeat_id=None):
    run, record = load_run(value)
    if record['status'] != 'JOB_PREPARED':
        raise ValueError('Launch exactly once from JOB_PREPARED; do not restart or resample')
    verify_current(record, codex=codex); verify_source(run, record, frozen=True)
    validate_job(run, record)
    if sha256(run/'workflow/job.json') != record['job_sha256']:
        raise ValueError('Prepared job changed before dispatch')
    command = [sys.executable, '-B', str(frozen_entry(run)), 'execute', str(run/'workflow'), '--detach']
    monitor = record_monitor(heartbeat_id, run, ROOT/'prepare_yui.py', record['configuration']['monitor'], write=write)
    write(run/'dispatch-attempt.json', {'argv': command, 'started_at_utc': utc()}, exclusive=True)
    update(run, record, 'DISPATCHING', launch_started_at_utc=utc(), model_started='POSSIBLE_AFTER_DISPATCH')
    try:
        value = json_process(command, timeout=180, log=run/'dispatch-result.json')
        if value.get('status') != 'DISPATCHED' or value.get('runs') != [str(run/'workflow')]:
            raise ValueError('Yui dispatch returned an unexpected result; inspect owned processes before any action')
        who = value.get('controller')
        if not isinstance(who, dict) or not all(who.get(k) is not None for k in ('pid', 'pgid', 'started')):
            raise ValueError('No complete detached controller identity; preserve and inspect this run')
        update(run, record, 'DISPATCHED', model_started=None, model_work_dispatched=True, dispatched_at_utc=utc())
    except Exception as error:
        fail(run, record, 'DISPATCH_ERROR', error)
        raise
    value['owner_observation'] = {**value.get('owner_observation', {}), **monitor}
    return value


def runtime_action(value, action):
    if action not in {'observe', 'cancel'}:
        raise ValueError('Unsupported owner action')
    run, record = load_run(value)
    if action == 'cancel' and record['status'] in {'SOURCE_REVIEW_REQUIRED', 'INPUTS_FROZEN', 'PREPARATION_FAILED', 'JOB_PREPARATION_FAILED'} and not (run/'workflow/job.json').exists() and not (run/'dispatch-attempt.json').exists():
        update(run, record, 'CANCELLED_PREPARATION', cancel_requested_at_utc=utc())
        return {'status': 'CANCELLED_PREPARATION', 'run': str(run), 'yui_model_dispatched': False,
                'scope': 'Preparation stopped; no Yui job was dispatched. Preserve inputs and owner accounting.'}
    value = json_process([sys.executable, '-B', str(frozen_entry(run)), action, str(run/'workflow')], timeout=60)
    if action == 'observe':
        cases = value.get('cases')
        if not isinstance(cases, list) or len(cases) != 1 or not isinstance(cases[0], dict) or cases[0].get('run') != str(run/'workflow'):
            raise ValueError('Observation does not belong to this run\'s exact workflow map')
        with owned_file(run, 'OWNER_MONITOR_LOG.jsonl').open('a') as out:
            out.write(json.dumps({'recorded_at_utc': utc(), 'observation': value})+'\n')
    else:
        update(run, record, 'CANCEL_REQUESTED', cancel_requested_at_utc=utc())
    return value


def terminal_ready(snapshot):
    if not isinstance(snapshot, dict):
        return False
    cases = snapshot.get('cases', [])
    if not isinstance(cases, list) or len(cases) != 1 or not isinstance(cases[0], dict):
        return False
    case = cases[0]
    counts = case.get('counts', {})
    if not isinstance(counts, dict):
        return False
    # A bound terminal result supersedes its last task counts and phase.
    status = case.get('recorded_result')
    if status is not None and (not isinstance(status, str) or status not in TERMINAL_OUTCOMES):
        return False
    if status is None and (case.get('phase') == 'PAUSED_ERROR' or counts.get('PAUSED_ERROR')):
        return False
    return (snapshot.get('all_terminal') is True and snapshot.get('all_process_exits_verified') is True
            and snapshot.get('process_inspection_error') is None and len(cases) == 1
            and cases[0].get('terminal_record_present') is True
            and cases[0].get('process_exit_verified') is True and cases[0].get('paused_errors') == []
            and type(cases[0].get('live_owned_process_count')) is int and cases[0].get('live_owned_process_count') == 0
            and cases[0].get('registered_groups_still_present') == [])


def validate_terminal(run):
    program = '''import json,sys
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
    installed = {'root': str(run/'workflow/runtime')}
    config = read(run/RECORD)['configuration']
    return runtime_program(installed, program, str(run/'workflow'), config['formalization'], timeout=180)


def finish(value):
    run, record = load_run(value)
    if (run/'FINAL_OUTCOME.json').exists():
        raise ValueError('Preserve the existing final outcome')
    snapshot = runtime_action(run, 'observe')
    if not terminal_ready(snapshot):
        raise ValueError('Not ready: a live/paused run or unverified process exit is not terminal')
    workflow = run/'workflow'
    case = read(owned_file(run, 'workflow/case-result.json'))
    if case.get('job') != {'path': str(workflow/'job.json'), 'sha256': sha256(workflow/'job.json')}:
        raise ValueError('Terminal result is not bound to this job')
    observed = snapshot['cases'][0].get('recorded_result')
    if case['result']['status'] not in TERMINAL_OUTCOMES:
        raise ValueError('Nonterminal case result cannot be finalized')
    if observed is not None and observed != case['result']['status']:
        raise ValueError('Terminal observation disagrees with the bound case result')
    validation = validate_terminal(run)
    result = case['result']
    end = datetime.fromtimestamp((workflow/'case-result.json').stat().st_mtime, timezone.utc)
    start = datetime.fromisoformat(record['started_at_utc'])
    launch_time = record.get('launch_started_at_utc')
    launched = datetime.fromisoformat(launch_time) if launch_time else end
    stage_health = []
    health_errors = []
    for path in sorted(workflow.rglob('result.json')):
        if {'runtime', 'harness-snapshot'} & set(path.relative_to(workflow).parts):
            continue
        try:
            data = read(owned_file(run, str(path.relative_to(run))))
        except (OSError, ValueError) as error:
            health_errors.append({'path': str(path.relative_to(workflow)), 'error': str(error)})
            continue
        if 'execution_health' not in data:
            continue
        stage_health.append({'path': str(path.relative_to(workflow)),
                             'execution_health': data.get('execution_health', 'UNKNOWN'),
                             'measurement_valid': data.get('measurement_valid')})
    final = {'schema': 'yui-benchmark-final-1', 'run': str(run), 'status': result.get('status'),
             'configuration': record['configuration'], 'runtime': record['bindings']['runtime'],
             'recorded_completion': result.get('completion'), 'bound_artifact_validation': validation,
             'source_warnings': result.get('warnings'), 'recorded_error': result.get('error'),
             'process_exit': snapshot, 'stage_execution_health': stage_health,
             'health_record_read_errors': health_errors,
             'health_scope': 'Retained result.json execution-health metadata, including proof workers; missing/unreadable diagnostics remain unknown, not fault-free.',
             'usage': result.get('usage', {'status': 'UNKNOWN'}),
             'timing': {'started_at_utc': record['started_at_utc'],
                        'launch_started_at_utc': launch_time,
                        'terminal_record_mtime_utc': end.isoformat(),
                        'preparation_wall_seconds': (launched-start).total_seconds(),
                        'recorded_case_seconds': result.get('elapsed_case_seconds'),
                        'total_to_terminal_record_seconds': (end-start).total_seconds(),
                        'owner_closed_at_utc': utc()},
             'scope': 'Read-only existing-artifact validation, not a new semantic review or Lean run; missing usage stays unknown and cached/reasoning counters are subsets.'}
    write(run/'FINAL_OUTCOME.json', final, exclusive=True)
    update(run, record, 'FINALIZED', finalized_at_utc=utc())
    return final


def cleanup_resources(value):
    run, record = load_run(value)
    if not (run/'workflow/case-result.json').is_file():
        raise ValueError('Cleanup requires an actual terminal case result; retain active/paused work')
    case = read(run/'workflow/case-result.json')
    if case.get('job') != {'path':str(run/'workflow/job.json'),'sha256':sha256(run/'workflow/job.json')}:
        raise ValueError('Cleanup result is not bound to this job')
    if sha256(owned_file(run,'workflow/job.json'))!=record['job_sha256']:
        raise ValueError('Prepared job changed before cleanup')
    frozen_entry(run); verify_source(run,record,frozen=True); validate_job(run,record)
    validate_terminal(run)
    helper=owned_file(run,'preparation/startup/resource_cleanup.py')
    if sha256(helper)!=record['bindings']['startup']['resource_cleanup.py']:
        raise ValueError('Cleanup helper changed')
    try:
        result=json_process([sys.executable,'-B',helper,str(run/'workflow'),str(run/'workflow/runtime')],timeout=180)
        validate_terminal(run)
    except Exception as error:
        write(run/'CLEANUP.json',{'status':'CLEANUP_BLOCKED','error':str(error)})
        raise
    write(run/'CLEANUP.json',result)
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    for command in ('check', 'begin', 'freeze', 'prepare', 'launch'):
        p = commands.add_parser(command)
        p.add_argument('--codex', type=Path)
        if command == 'launch':
            p.add_argument('--heartbeat-id', help='Optional existing heartbeat ID on a host that permits this handoff; omit for in-chat waiting')
        if command == 'begin':
            p.add_argument('--run-id')
        elif command != 'check':
            p.add_argument('run', type=Path)
    for command in ('observe', 'cancel', 'finish', 'cleanup'):
        commands.add_parser(command).add_argument('run', type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == 'check':
            config, installed, bound, environment = checked_environment(args.codex)
            result = {'status': 'ENVIRONMENT-CHECKED', 'configuration': config, 'installed': installed,
                      'bindings': bound, 'environment': environment, 'model_started': False}
        elif args.command == 'begin':
            result = begin(codex=args.codex, run_id=args.run_id)
        elif args.command == 'launch':
            result = launch(args.run, codex=args.codex, heartbeat_id=args.heartbeat_id)
        elif args.command in {'freeze', 'prepare'}:
            result = globals()[args.command](args.run, codex=args.codex)
        elif args.command == 'finish':
            result = finish(args.run)
        elif args.command == 'cleanup':
            result = cleanup_resources(args.run)
        else:
            result = runtime_action(args.run, args.command)
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(json.dumps({'status': 'BENCHMARK_ACTION_BLOCKED', 'action': args.command,
                          'error': type(error).__name__+': '+str(error),
                          'run': getattr(error, 'run', str(args.run) if hasattr(args, 'run') else None),
                          'automatic_retry': False}, indent=2))
        return 1
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
