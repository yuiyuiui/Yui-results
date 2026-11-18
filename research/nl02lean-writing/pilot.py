"""Run one fixed-model paired-experiment arm on a frozen local source packet."""

import argparse
import json
from pathlib import Path
import subprocess
import sys
import time


PROFILE = {'id': 'gpt-6.1-sol', 'reasoning_effort': 'high',
           'speed': 'standard', 'automatic_fallback': False}


def trial(yui, plan_path, step, arm, out, seconds):
    sys.path[:0] = [str(yui / 'nl02lean/scripts'), str(yui / 'nl0/scripts')]
    import concurrency
    import execution_state as execution
    import ir
    import lean_task
    from model_pilot import Stage
    import run_graph
    from runtime_config import use_profiles, scientific_pins

    with use_profiles({'nl0': PROFILE, 'lean': PROFILE}):
        cpath, plan = run_graph.package(plan_path.with_name('contract.json'), plan_path, out)
        tasks = lean_task.prepare_run(out, cpath, None)
        request = lean_task.issue(out, cpath, step, ir.local_packet(cpath, plan, step), tasks)
        stage = Stage(out / 'author', cpath, 'proof', seconds, plan, step,
                      task_request=request, draft_revisions=(arm == 'edit'))
        recorder = execution.Recorder(out, f'{step}-{arm}', concurrency.resolve(1),
                                      time_budget_seconds=seconds)
        started = time.monotonic()
        checked, status = None, None
        try:
            with recorder.signals(), execution.activate(recorder, step):
                try:
                    status, proof = stage.execute()
                except execution.CaseDeadlineExceeded:
                    status = ir.load(stage.logs / 'result.json')
                elapsed = time.monotonic() - started
            if proof and status['status'] == 'ACCEPTED':
                checked = ir.check(cpath, plan, {step: proof['proof']}, only=step,
                                   out=out / 'independent-recheck', timeout=60)
        finally:
            # The local experiment is now terminal. Preserve proof and carrier logs.
            if not getattr(stage, '_resources_released', False):
                stage.release_resources('WORKFLOW_FINALIZED')
            if checked is not None and ir.native_succeeded(checked):
                terminal = 'LOCAL_CHECKED'
            elif status is not None and status['status'] == 'UNFINISHED':
                terminal = 'UNFINISHED'
            else:
                terminal = 'FINISHED'
            recorder.task(step, state=terminal, activity='BENCHMARK_TERMINAL',
                          finished_at_utc=execution.now())
            recorder.close('BENCHMARK_TERMINAL')
        tools_file = stage.logs / 'tools.jsonl'
        calls = [json.loads(line) for line in tools_file.read_text().splitlines()] if tools_file.is_file() else []
        proof_calls = [row for row in calls if row['tool'] in ('check_transition', 'submit_transition')]
        measures = {
            'model': PROFILE,
            'pins': scientific_pins(),
            'yui_revision': subprocess.check_output(['git', '-C', yui, 'rev-parse', 'HEAD'], text=True).strip(),
            'contract_sha256': ir.digest(cpath),
            'plan_sha256': ir.digest(out / 'inputs/plan.json'),
            'step': step,
            'arm': arm,
            'budget_s': seconds,
            'time_s': round(elapsed, 3),
            'status': status['status'],
            'outcome': status.get('task_outcome'),
            'stop_reason': status.get('stop_reason'),
            'execution_health': status.get('execution_health'),
            'measurement_valid': status.get('measurement_valid'),
            'usage': status.get('usage'),
            'native_turns': status.get('native_turns'),
            'tool_calls': len(calls),
            'proof_checks': len(proof_calls),
            'proof_edit_calls': sum('edit' in row['arguments'] for row in proof_calls),
            'lean_calls': status.get('lean_calls'),
            'lean_native_wall_s': round(sum(row['result'].get('wall_seconds', 0)
                for row in calls if 'exit_code' in row['result']), 3),
            'proof_wire_bytes': sum(len(json.dumps(row['arguments'], ensure_ascii=False,
                separators=(',', ':')).encode()) for row in proof_calls),
            'independent_recheck': checked['status'] if checked else None,
            'independent_axioms': checked.get('axioms') if checked else None,
        }
        ir.write(out / 'measures.json', measures)
        return measures


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--yui', type=Path, required=True)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--step', required=True)
    parser.add_argument('--arm', choices=['full', 'edit'], required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--seconds', type=int, required=True)
    args = parser.parse_args()
    print(json.dumps(trial(args.yui.resolve(), args.plan.resolve(), args.step,
                           args.arm, args.out.resolve(), args.seconds), indent=2))


if __name__ == '__main__':
    main()
