#!/usr/bin/env python3
"""Check prerequisites and prepare a future task; never dispatch mathematical work."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import sys

from benchmark_config import ROOT, load_config, local_path
from skill_check import NAME, require_skill

STARTUP_FILES = ('AGENTS.md', 'README.md', 'settings.json', 'benchmark_config.py',
                 'skill_check.py', 'prepare_yui.py')
PREPARED = ROOT / '.prepared'


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def runtime_binding(installed):
    root = Path(installed['root'])
    rows = {}
    for name in ['SKILL.md', 'config.json', 'nl0', 'nl02lean', 'toolchain']:
        start = root / name
        paths = [start] if start.is_file() else start.rglob('*')
        for path in paths:
            if '__pycache__' in path.parts or 'tests' in path.relative_to(root).parts:
                continue
            if path.is_file() and path.suffix in {'.py', '.md', '.json', '.mjs', '.lean'}:
                rows[str(path.relative_to(root))] = sha256(path)
    digest = hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest()
    commit = subprocess.run(['git', '-C', str(root), 'rev-parse', 'HEAD'],
                            text=True, capture_output=True, check=False)
    return {'sha256': digest, 'files': len(rows),
            'source_commit': commit.stdout.strip() if commit.returncode == 0 else None}


def invocation(paper, workers, installed, *, config=None):
    config = load_config() if config is None else config
    paper = Path(paper).expanduser().resolve()
    if not paper.is_file():
        raise FileNotFoundError('Supply the local original paper PDF')
    if type(workers) is not int or workers < 1 or workers != config['workers']:
        raise ValueError('Worker count must match the explicitly selected local settings')
    if installed['name'] != config['skill_name']:
        raise ValueError('This directory requires exactly $'+config['skill_name'])
    output = local_path(config['results_directory'])
    verify_command = shlex.join(['python3', '-B', str(ROOT / 'prepare_yui.py'), '--verify-preparation'])
    return f'''Use ${config['skill_name']} for {config['benchmark_name']}'s full normal-policy workflow.

Start only after the human explicitly authorizes this benchmark. A preparation
file is not start authorization. A subsequent explicit dispatch message can
supply that authorization; retain the settings already recorded here.

Read only this benchmark's AGENTS.md, README.md and settings.json, and the
installed skill entry below. Recheck the local preparation before dispatch:
{verify_command}
Installed entry: {installed['skill_md']}
Use that exact registered skill and its bundled runtime. Do not substitute
rigorous-proof-development, another variant, or an unregistered checkout.

Original paper: {paper}
Original PDF SHA-256: {sha256(paper)}
Target: {config['target']}
Read the original and freeze the complete source-faithful target under the
selected skill's rules, checking that PDF extraction preserves its mathematics.
Do not replace the numerical method or omit a hypothesis or conclusion.
The PDF is the only initial mathematical input. Do not import an old draft,
NL0, theorem list, source cache, proof, review, or result from another run.

Produce NL0, complete independent Audit A, typed interfaces with
pre-freeze independent semantic review, Lean proofs, standalone assembly/native trust inspection,
and machine Audit B inheriting the reviewed frozen-interface authority.
Use exceptional B-final semantic review only where the existing workflow requires it,
retaining its actual warnings and qualifications.
Both phase profiles are gpt-6.1-sol / high / Standard,
without fallback. The explicitly selected per-case worker count is {workers},
for local R reviews and later local Lean proofs in separate phases. NL0 author,
global A, preparation/interfaces, assembly and B keep their serial lanes.
There is no total time, token or call budget. Each native Lean call retains
the selected skill's {config['limits']['native_seconds']}-second limit and its ordinary located repair rules.

Create a fresh unique run directory under {output} and supply it explicitly
as --out. Never use a skill-default output elsewhere or overwrite an old run.
Keep runtime snapshots, original/extracted inputs, the source target, job/config,
proofs, reviews, native checks, warnings, usage and execution evidence together.
Copy the local preparation/task prompt into owner provenance, outside measured
mathematical input packets. Record actual installed/runtime hashes and commits.
Read no sibling benchmark, direct-model subtree, archived test or other-arm
partial result. Give measured sessions only this run's declared materials and
selected skill rules. Supply no outside mathematical hints or personal skills.

At invocation disclose conditional-source handling. Use the skill's ordinary
retrieval and review; inaccessible originals remain explicit warn.json/warn.md
qualifications. Never silently count a qualified result as unconditional PASS.

Dispatch with --detach, verify actual PID, OS start identity and PGID, register
one real host heartbeat every 600 seconds, save its ID/current run map in
OWNER_MONITOR_STATE.json, then end the foreground turn. Each wake performs one
bounded observation and ends. Notify briefly in Chinese on meaningful change,
fault, completion or required action; unchanged routine checks stay quiet.
Do not keep a foreground sleep/poll loop. If scheduling is unavailable, disclose
the limitation and return observation/cancellation commands.

Let the normal controller repair within its supported boundaries. Do not
restart live work, bypass guards, edit a bound runtime, silently reset costs,
or resample a mathematical nonpass. Record actual failures and every authorized
continuation separately; report unsupported blockers with their retained state.

At termination validate existing bound result/A/B artifacts with the selected
skill's validators, without launching an additional model or proof run. Keep
structural acceptance, conditional local proofs, standalone assembly, native
trust inspection, pre-freeze semantic review, machine Audit B and any exceptional
B-final review distinct. Report the complete
target and every external-theorem correspondence, warnings, actual phase,
wall time, phase times, known/partial tokens and missing coverage. Sum distinct
responses only; cached/reasoning counts are subsets. Record requested and
observed model/effort/tier; an absent actual tier stays unverified.
Preserve every attempt's cost, confirm exact owned processes/groups exited,
save FINAL_OUTCOME.json and the final human report under this run, delete its
completed heartbeat, and end. Do not evaluate or read the other benchmark's
proof while either construction is active. The coordinating owner compares
the two terminal results afterwards, outside both construction sessions.
Concurrent runs share host/account resources; no isolated speed claim follows.
'''


def environment_check(installed, config):
    # Trusted functions inspect versions, pins and local metadata. No model,
    # theorem probe, prepare/run/execute command or Lean build is invoked.
    program = '''import hashlib,json,sys,shutil
from pathlib import Path
root=Path(sys.argv[1]);paper=Path(sys.argv[2]);config=json.load(sys.stdin)
sys.path[:0]=[str(root/'nl0/scripts'),str(root/'nl02lean/scripts')]
from runtime_config import verify,auth_home,native_timeout
from entrypoint import preflight_profiles
from target_selection import text
preflight_profiles({'track':config['track'],'profiles':config['profiles']})
if not (auth_home()/'auth.json').is_file():raise ValueError('Codex authentication file is absent')
runtime=json.loads((root/'config.json').read_text())
if runtime['timeouts']!={'case_seconds':None,'stage_seconds':None,'native_seconds':config['limits']['native_seconds']} or runtime['token_budget'] is not None:
 raise ValueError('Installed timeout/token policy differs from this benchmark')
if native_timeout()!=config['limits']['native_seconds']:raise ValueError('Native-call limit differs')
environment=verify();extracted=text(paper)
if not extracted.strip():raise ValueError('Original PDF has no readable extracted text')
print(json.dumps({'status':'ENVIRONMENT-CHECKED','resolved_environment':environment,
 'profile_metadata_verified':True,'authentication_file_present':True,
 'pdf_extraction':{'method':'pdftotext-layout' if shutil.which('pdftotext') else 'pypdf-text',
 'characters':len(extracted),'text_sha256':hashlib.sha256(extracted.encode()).hexdigest(),
 'mathematical_fidelity':'OWNER_MUST_CHECK_BEFORE_TARGET_FREEZE'},
 'model_started':False,'proof_check_started':False,'actual_service_tier':None,
 'provider_quota_verified':False}))
'''
    result = subprocess.run([sys.executable, '-B', '-c', program, installed['root'],
                             str(local_path(config['paper']))], input=json.dumps(config),
                            capture_output=True, text=True, timeout=60, check=False)
    if result.returncode:
        raise ValueError('Read-only environment preflight failed: '+result.stderr[-2500:])
    return json.loads(result.stdout)


def bindings(installed, config):
    return {'startup': {name: sha256(ROOT / name) for name in STARTUP_FILES},
            'paper_sha256': sha256(local_path(config['paper'])),
            'installed': {key: installed[key] for key in ['name', 'skill_md', 'root', 'skill_sha256']},
            'runtime': runtime_binding(installed)}


def preparation(installed, config):
    prompt = invocation(local_path(config['paper']), config['workers'], installed, config=config)
    return {'schema_version': 'yui-benchmark-preparation-1',
            'status': 'READY_AWAITING_USER_START',
            'prepared_at_utc': datetime.now(timezone.utc).isoformat(),
            'benchmark_name': config['benchmark_name'], 'configuration': config,
            'bindings': bindings(installed, config),
            'environment': environment_check(installed, config),
            'task_prompt_sha256': hashlib.sha256(prompt.encode()).hexdigest(),
            'model_started': False, 'workflow_created': False, 'start_authorized': False,
            'quota_and_future_network_health': 'UNVERIFIED', 'prompt': prompt}


def verify_preparation(installed, config):
    record = json.loads((PREPARED / 'readiness.json').read_text())
    if record.get('schema_version') != 'yui-benchmark-preparation-1':
        raise ValueError('Unsupported preparation record')
    prompt = invocation(local_path(config['paper']), config['workers'], installed, config=config)
    if (record['configuration'] != config or record['bindings'] != bindings(installed, config)
            or sha256(PREPARED / 'task.md') != record['task_prompt_sha256']
            or hashlib.sha256(prompt.encode()).hexdigest() != record['task_prompt_sha256']):
        raise ValueError('Preparation is stale: input, configuration, instructions or installed runtime changed')
    current = environment_check(installed, config)
    if record['environment'] != current:
        raise ValueError('Preparation is stale: resolved tools or PDF extraction changed')
    return {'status': 'PREPARATION_VALID_AWAITING_USER_START', 'model_started': False,
            'workflow_created': False, 'start_authorized': False,
            'benchmark_name': config['benchmark_name'], 'skill': installed['name'],
            'workers': config['workers'], 'task_prompt': str(PREPARED / 'task.md')}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--codex', type=Path)
    parser.add_argument('--skill', choices=[NAME], default=NAME)
    parser.add_argument('--workers', type=int, help='Must match the already selected local settings')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write-preparation', action='store_true')
    mode.add_argument('--verify-preparation', action='store_true')
    args = parser.parse_args(argv)
    try:
        config = load_config()
        if args.workers is not None and args.workers != config['workers']:
            raise ValueError('Worker count differs from settings.json; reconcile both arms before preparation')
        installed = require_skill(codex=args.codex, skill_name=config['skill_name'])
        if args.verify_preparation:
            result = verify_preparation(installed, config)
        else:
            result = preparation(installed, config)
            if args.write_preparation:
                if PREPARED.is_symlink():
                    raise ValueError('Preparation directory must not be a symlink')
                PREPARED.mkdir(exist_ok=True)
                prompt = result.pop('prompt')
                (PREPARED / 'task.md').write_text(prompt)
                (PREPARED / 'readiness.json').write_text(json.dumps(result, indent=2)+'\n')
                result = {'status': result['status'], 'model_started': False, 'workflow_created': False,
                          'start_authorized': False, 'workers': config['workers'],
                          'skill': installed['name'], 'readiness': str(PREPARED / 'readiness.json'),
                          'task_prompt': str(PREPARED / 'task.md')}
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(json.dumps({'status': 'BENCHMARK_NOT_STARTED', 'error': str(error)})); return 1
    print(json.dumps(result, indent=2)); return 0


if __name__ == '__main__':
    raise SystemExit(main())
