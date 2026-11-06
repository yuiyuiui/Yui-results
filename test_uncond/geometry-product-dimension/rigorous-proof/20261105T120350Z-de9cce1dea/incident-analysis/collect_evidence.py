"""Read retained records and generate incident appendices; no model or Lean calls.

Run with python3 -B. Writes only this incident-analysis directory. Does not
resume, repair, cancel, clean, or change any scientific/lifecycle record.
"""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib
import importlib.util
import json
import re

OUT = Path(__file__).resolve().parent
RUN = OUT.parent
WORK = RUN / 'workflow'
SOURCES = set()


def read(path):
    path = Path(path)
    SOURCES.add(path)
    return path.read_text()


def load(path):
    return json.loads(read(path))


def write(name, data):
    (OUT / name).write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def local_time(value):
    return datetime.fromisoformat(value).astimezone(ZoneInfo('Asia/Shanghai')).isoformat()


def rel(path):
    return str(Path(path).relative_to(RUN))


def link(path):
    return f'[{rel(path)}](../{rel(path)})'


final = load(RUN / 'OWNER_FINAL_REPORT.json')
case = load(WORK / 'case-result.json')
test = load(RUN / 'TEST_RUN.json')
status = load(WORK / 'execution-status.json')
observations = [json.loads(line) for line in read(RUN / 'OWNER_MONITOR_LOG.jsonl').splitlines()]
cleanup = load(RUN / 'CLEANUP.json')
monitor = load(RUN / 'OWNER_MONITOR_STATE.json')
job = load(WORK / 'job.json')

rows = []
for usage_path in final['usage']['final_ledger_reconciliation']['stage_usage_files']:
    up = Path(usage_path)
    usage = load(up)
    path = up.parent / 'result.json'
    data = load(path)
    rows.append({
        'result': rel(path), 'usage': rel(up),
        **{key: data.get(key) for key in ['mode', 'status', 'task_outcome', 'acceptance_scope',
            'started_at_utc', 'finished_at_utc', 'wall_seconds', 'lean_calls', 'remote_retries',
            'execution_health', 'identity_and_input_boundary_verified', 'native_thread_id']},
        'observed_usage': data.get('usage', {}).get('observed_usage'),
    })
rows.sort(key=lambda row: row['started_at_utc'])
write('STAGE_TIMELINE.json', rows)
timeline = ['# Retained stage timeline', '',
    'All displayed times use Asia/Shanghai (UTC+08:00). Intervals overlap. '
    'A stage `ACCEPTED` label has its recorded scope; it does not establish whole-workflow acceptance.', '',
    '| Start | Finish | Stage | Status | Recorded wall seconds | Lean calls |',
    '| --- | --- | --- | --- | ---: | ---: |']
for row in rows:
    timeline.append(f"| {local_time(row['started_at_utc'])[11:19]} | "
        f"{local_time(row['finished_at_utc'])[11:19]} | [{row['result']}](../{row['result']}) | "
        f"{row['status']} | {row['wall_seconds']:.3f} | {row['lean_calls']} |")
(OUT / 'STAGE_TIMELINE.md').write_text('\n'.join(timeline) + '\n')

appendix = ['# Exact retained evidence excerpts', '',
    'Generated from the named retained files. These are historical model reports, '
    'compiler outputs and source excerpts, with their original evidentiary limits. '
    'No new mathematical review or compiler execution is performed.', '']


def section(title, path, value=None, language='json'):
    text = read(path) if value is None else value
    SOURCES.add(Path(path))
    appendix.extend([f'## {title}', '', link(path), '', f'```{language}', text.rstrip(), '```', ''])


diagpath = WORK / 'nl0-to-lean/0002/interface/inputs/repair-diagnostics.json'
diagnostics = load(diagpath)['report']['diagnoses']
for node, diagnosis in sorted(diagnostics.items()):
    section(f'{node}: full independent diagnostic', diagpath,
            json.dumps(diagnosis, ensure_ascii=False, indent=2))
    parent = WORK / 'nl0-to-lean/0001/workflow/proof-run/workers' / node
    for path in parent.glob('diagnosis-requests/*/review/inputs/own-attempts.json'):
        attempts = load(path)
        for index, attempt in enumerate(attempts):
            actual = attempt.get('actual_attempt', {})
            check = actual.get('check', {})
            if check:
                section(f'{node}: attempt {index}, retained compiler result', path,
                    json.dumps(check, ensure_ascii=False, indent=2))

base = WORK / 'nl0-to-lean/0002/interface'
section('Blocked interface author: exact obstacle', base / 'stage/accepted.json')
tools = [json.loads(line) for line in read(base / 'stage/tools.jsonl').splitlines()]
selected_tools = []
for index, call in enumerate(tools, 1):
    if call.get('tool') in {'check_lean_types', 'check_draft', 'save_interface_draft',
                            'report_obstacle'} or call.get('result', {}).get('accepted') is False:
        selected_tools.append({'ordinal_in_tools_jsonl': index, **call})
        # Full arguments/results are useful here, including rejected alternative probes.
        section(f'Blocked interface tool call {index}: {call.get("tool")}',
            base / 'stage/tools.jsonl', json.dumps(call, ensure_ascii=False, indent=2))
write('REPAIR_TOOL_CALLS.json', selected_tools)
for path in sorted((base / 'candidates').glob('*/explicit-edits.json')):
    section(f'Candidate {path.parent.name}: exact edits', path)
section('Candidate 2: full native strict-type result', base / 'candidates/0002/types/result.json')
section('Candidate 2: exact generated Lean', base / 'candidates/0002/types/Check.lean', language='lean')
section('Initial independent semantic review',
        WORK / 'nl0-to-lean/0001/interface-review/stage/accepted.json')
section('Retained controller incident', WORK / 'logs/controller-errors/error-state.json')

snippets = [
    ('Emitter and local packet', WORK / 'runtime/nl02lean/scripts/ir.py', [(60, 82), (152, 182), (249, 265), (294, 338)]),
    ('Interface schema and repair prompt', WORK / 'runtime/nl02lean/scripts/translation_author.py', [(85, 113), (159, 170), (214, 228)]),
    ('Protected internal repair', WORK / 'runtime/nl02lean/scripts/internal_interface_repair.py', [(1, 12), (39, 57)]),
    ('Owner observation projection', WORK / 'runtime/nl0/scripts/owner_observation.py', [(130, 180)]),
    ('Entry terminal predicate', RUN / 'preparation/startup/entry_support/common.py', [(113, 140)]),
    ('Entry finish and cleanup', RUN / 'preparation/startup/entry_support/exercise_entry.py', [(240, 281)]),
]
for title, path, ranges in snippets:
    lines = read(path).splitlines()
    content = '\n\n'.join('\n'.join(f'{i}: {lines[i-1]}' for i in range(start, min(end, len(lines))+1))
                           for start, end in ranges)
    section(title, path, content, language='text')

# Evaluate only the trusted, recorded entry's pure predicate on saved snapshots.
module_path = RUN / 'preparation/startup/entry_support/common.py'
spec = importlib.util.spec_from_file_location('incident_entry_common', module_path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
last = observations[-1]['observation']
counterfactual = json.loads(json.dumps(last))
counterfactual['cases'][0]['counts']['PAUSED_ERROR'] = 0
predicate = {
    'source': rel(module_path), 'input_source': 'OWNER_MONITOR_LOG.jsonl:last observation',
    'actual_result': module.terminal_ready(last),
    'actual_all_terminal': last['all_terminal'],
    'actual_all_process_exits_verified': last['all_process_exits_verified'],
    'actual_paused_errors': last['cases'][0]['paused_errors'],
    'actual_counts': last['cases'][0]['counts'],
    'counterfactual_in_memory_only': {
        'change': '/cases/0/counts/PAUSED_ERROR: 1 -> 0',
        'result': module.terminal_ready(counterfactual),
        'interpretation': 'Isolates the blocking boolean in this record; does not authorize ignoring real active pauses.',
    },
    'models_started': False, 'lean_checks_started': False, 'bound_records_modified': False,
}
write('TERMINAL_PREDICATE_REPRODUCTION.json', predicate)
appendix.extend(['## Pure terminal predicate reproduction', '', '```json',
                 json.dumps(predicate, ensure_ascii=False, indent=2), '```', ''])
(OUT / 'EVIDENCE_APPENDIX.md').write_text('\n'.join(appendix))

snapshot = {
    'schema': 'yui-incident-evidence-1', 'run': str(RUN),
    'configuration': test['configuration'], 'original_bindings': test['bindings'],
    'frozen_runtime_sha256': test['frozen_runtime_sha256'],
    'job_sha256': test['job_sha256'],
    'result_summary': {key: case['result'].get(key) for key in ['status','task_outcome',
        'elapsed_case_seconds','completion','formalization_goal','retained_error']},
    'usage': final['usage'], 'validation': final['validation'],
    'cleanup': cleanup, 'monitor': monitor,
    'observations': observations,
    'actual_proof_node_ids': [s['id'] for s in load(base / 'inputs/prior-interface.json')['steps']],
    'terminal_predicate': predicate,
    'source_manifest': [{'path': rel(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                         'bytes': path.stat().st_size} for path in sorted(SOURCES)],
}
write('EVIDENCE.json', snapshot)
print(json.dumps({'stages': len(rows), 'source_files': len(SOURCES),
                  'selected_repair_calls': len(selected_tools),
                  'actual_terminal_predicate': predicate['actual_result'],
                  'counterfactual_terminal_predicate': predicate['counterfactual_in_memory_only']['result'],
                  'output': str(OUT)}, indent=2))
