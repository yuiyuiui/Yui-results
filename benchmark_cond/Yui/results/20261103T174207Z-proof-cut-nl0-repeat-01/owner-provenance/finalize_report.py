"""Summarize this terminal run's existing evidence; no model or Lean execution."""
from pathlib import Path
from datetime import datetime, timezone
from zoneinfo import ZoneInfo
from collections import Counter, defaultdict
import hashlib
import json
import re

ROOT = Path('/Users/syyui/projects/Yui-results/benchmark/results/20261103T174207Z-proof-cut-nl0-repeat-01')
PACKET = Path('/Users/syyui/projects/Yui-results/benchmark/handoffs/20261103T174207Z-codex-codex-INDEPENDENT-01')
PROV = ROOT / 'owner-provenance'
READS = set()


def read(path):
    path = Path(path)
    READS.add(str(path))
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_new(path, data):
    with Path(path).open('x') as handle:
        json.dump(data, handle, ensure_ascii=False, indent=2)
        handle.write('\n')


def dt(value):
    return datetime.fromisoformat(value)


def local_time(value):
    return dt(value).astimezone(ZoneInfo('Asia/Shanghai')).strftime('%Y-%m-%d %H:%M:%S')


def graph_counts(path):
    graph = read(path)
    props, infs = graph['propositions'], graph['inferences']
    return {
        'path': str(path), 'sha256': digest(path),
        'N': sum(p['kind'] == 'internal' for p in props), 'R': len(infs),
        'S': sum(len(r['argument']) for r in infs),
        'F': sum(len(s.get('produces', [])) for r in infs for s in r['argument']),
        'proposition_kinds': dict(Counter(p['kind'] for p in props)),
        'per_R': [{'id': r['id'], 'output': r['output'], 'S': len(r['argument']),
                   'F': sum(len(s.get('produces', [])) for s in r['argument'])} for r in infs],
    }


def group_time(rows):
    start = min(dt(r['started_at_utc']) for r in rows)
    end = max(dt(r['finished_at_utc']) for r in rows)
    return {
        'stages': len(rows), 'started_at_utc': start.isoformat(), 'finished_at_utc': end.isoformat(),
        'timestamp_span_seconds': (end-start).total_seconds(),
        'sum_recorded_stage_wall_seconds': sum(r['wall_seconds'] for r in rows),
        'definition': 'Span includes inter-stage gaps within the group. Stage wall sums can overlap, include tools/waits, and are not pure model reasoning time.',
    }


state = read(ROOT/'OWNER_MONITOR_STATE.json')
assert state['automation_id'] == 'yui-nl0-01'
assert [r['run'] for r in state['current_run_map']] == [str(ROOT)]
observation = state['last_observation']
assert observation['all_terminal'] and observation['all_process_exits_verified']
assert observation['cases'][0]['live_owned_process_count'] == 0
assert not observation['cases'][0]['registered_groups_still_present']
assert not state['recovery_authorized']
case = read(ROOT/'case-result.json')
result = case['result']
job = read(ROOT/'job.json')
status = read(ROOT/'execution-status.json')
batch = read(ROOT/'batch-result.json')
launch = read(PACKET/'return/execute-command.json')
preflight = read(PROV/'launch-preflight.json')
check_record = read(PROV/'terminal-validation/audit-a-check.json')
check = check_record['parsed_result']
metrics_failure = read(PROV/'terminal-validation/metrics.json')
assert result['status'] == 'DRAFT-AUDIT-PASSED'
assert result['acceptance_scope'] == 'NL0_AND_AUDIT_A_ONLY'
assert result['completion']['acceptance_target_satisfied']
assert job['track'] == 'nl0' and job['policy'] == 'normal' and job['max_concurrency'] == 20
assert digest(ROOT/'job.json') == case['job']['sha256']
assert check_record['exit_code'] == 0
assert check['current_standard_receipt_valid'] and check['audit_receipt_valid']
assert check['independent_review_accepted'] and check['audit_record_complete']
assert not check['unresolved_reviews'] and not check['source_warnings']
assert not check['mathematics_automatically_verified']
assert batch['children_exited'] and not batch['unconfirmed_pids']
assert status['cancellation']['cleanup'] == 'CONFIRMED_NO_OWNED_PROCESSES'
assert not status['cancellation']['resource_cleanup_errors']
assert not status['cancellation']['requests']
runtime_manifest = read(ROOT/'runtime-manifest.json')
assert digest(ROOT/'runtime-manifest.json') == job['runtime_snapshot']['manifest']['sha256']
for item in runtime_manifest['files']:
    assert digest(ROOT/'runtime'/item['relative_path']) == item['sha256']
for doc in job['documents']:
    assert digest(ROOT/'inputs'/doc['path']) == doc['sha256']
    assert digest(doc['original']['path']) == doc['original']['sha256']
source = result['source']
spec = read(source['spec'])
audit = read(source['audit_a'])
graph = read(source['graph'])
assert spec['full_target'] == job['target_selection']['full_target']
assert (ROOT/'inputs/target-selection.json').read_bytes() == (PACKET/'frozen/02-target-selection.json').read_bytes()
assert all(v['verdict'] == 'PASS' for v in audit['inference_reviews'].values())
assert all(v['verdict'] == 'PASS' for v in audit['source_reviews'].values())
assert all(c['verdict'] == 'PASS' for v in audit['source_reviews'].values() for c in v['citation_checks'].values())
assert all(p['state'] == 'EXITED' for p in status['processes'].values())
for rel in ['audit-a/0001-0001/global-acceptance.json', 'audit-a/0002-0013/global-acceptance.json']:
    gate = read(ROOT/rel)
    assert gate['accepted'] and gate['complete'] and not gate['conditional']

stages = []
for path, binding in status['stage_history'].items():
    assert Path(path).is_relative_to(ROOT)
    assert digest(path) == binding['record']['sha256']
    value = read(path)
    rel = str(Path(path).relative_to(ROOT))
    row = {k: value.get(k) for k in ['mode', 'status', 'started_at_utc', 'finished_at_utc', 'wall_seconds',
            'execution_health', 'execution_qualified', 'identity_and_input_boundary_verified', 'remote_retries',
            'error_pauses', 'continuations', 'lean_calls', 'native_turns', 'native_thread_id', 'model_selection']}
    row.update(path=rel, sha256=digest(path), role_session=value.get('role_session'),
               native_faults=value.get('transport_health', {}).get('faults', []),
               usage=value['usage']['observed_usage'], actual_model_ids=value.get('exposure', {}).get('actual_model_ids', []),
               observed_service_tiers=value['usage'].get('observed_service_tiers', []),
               measurement_complete=value.get('measurement_complete'))
    accepted_path = Path(path).parent/'accepted.json'
    accepted = read(accepted_path)
    if row['mode'] == 'audit-a-packet-replay':
        row['R'] = re.search(r'/R(\d{3})/stage/', rel).group(1)
        row['R'] = 'R'+row['R']
        row['mathematical_verdict'] = accepted.get('verdict')
    elif row['mode'] == 'nl0-local-repair':
        row['R'] = re.search(r'-R(\d{3})-', rel).group(1)
        row['R'] = 'R'+row['R']
        row['repair_artifact_type'] = accepted.get('status', 'OWN_INFERENCE_PATCH')
        row['local_structural_candidate_directories'] = len(list(Path(path).parent.parent.glob('candidates/[0-9]*')))
    if row['mode'] == 'nl0-authoring':
        row['author_candidate_count'] = len(list((Path(path).parent/'case').glob('candidate-*.json')))
    stages.append(row)
stages.sort(key=lambda r: r['started_at_utc'])
assert len({r['path'] for r in stages}) == len(stages) == 25
assert all(r['identity_and_input_boundary_verified'] for r in stages)
tokens = {k: sum(r['usage'][k] for r in stages) for k in ['input_tokens', 'output_tokens', 'total_tokens', 'cached_input_tokens', 'reasoning_tokens']}
assert tokens == result['usage']['confirmed_tokens']
assert tokens['input_tokens']+tokens['output_tokens'] == tokens['total_tokens']
assert set(result['usage']['final_ledger_reconciliation']['stage_usage_files']) == {str(ROOT/r['path']).removesuffix('result.json')+'usage.json' for r in stages}
assert not result['usage']['final_ledger_reconciliation']['missing_ledgers']
assert sum(r['lean_calls'] for r in stages) == 0
groups = {
    'initial_NL0': [r for r in stages if r['path'].startswith('nl0/0001-')],
    'first_global_A': [r for r in stages if r['path'].startswith('audit-a/0001-')],
    'first_local_A_including_local_repairs': [r for r in stages if '/local-0001-' in r['path']],
    'restored_global_author_repair': [r for r in stages if r['path'].startswith('nl0/0002-')],
    'second_global_A': [r for r in stages if r['path'].startswith('audit-a/0002-')],
    'second_local_A_including_local_repairs': [r for r in stages if '/local-0002-' in r['path']],
}
phase_times = {name: group_time(rows) for name, rows in groups.items()}
graphs = [graph_counts(ROOT/p) for p in ['nl0/0001-0001/stage/case/nl0.json', 'nl0/merged-0001/nl0.json',
          'nl0/0002-0013/stage/case/nl0.json', 'nl0/merged-0002/nl0.json']]
work = []
for r in graphs[-1]['per_R']:
    local = [v for v in stages if v.get('R') == r['id']]
    review = [v for v in local if v['mode'] == 'audit-a-packet-replay']
    repair = [v for v in local if v['mode'] == 'nl0-local-repair']
    work.append({**r, 'review_stages': len(review), 'repair_stages': len(repair),
                 'global_escalations': sum(v.get('repair_artifact_type') == 'GLOBAL_REPAIR_REQUIRED' for v in repair),
                 'review_wall_sum_seconds': sum(v['wall_seconds'] for v in review),
                 'repair_wall_sum_seconds': sum(v['wall_seconds'] for v in repair),
                 'first_review_verdict': review[0]['mathematical_verdict'],
                 'review_verdict_history': [v['mathematical_verdict'] for v in review],
                 'observed_input_tokens': sum(v['usage']['input_tokens'] for v in local),
                 'observed_output_tokens': sum(v['usage']['output_tokens'] for v in local),
                 'observed_total_tokens': sum(v['usage']['total_tokens'] for v in local),
                 'stages': [v['path'] for v in local]})
faults = [{'path': r['path'], 'execution_health': r['execution_health'],
           'execution_qualified': r['execution_qualified'], 'faults': r['native_faults']} for r in stages if r['native_faults'] or r['execution_health'] != 'NO_RECORDED_FAULT']
assert len(faults) == 1 and sum(len(v['faults']) for v in faults) == 1
assert {w['id'] for w in work if w['first_review_verdict'] != 'PASS'} == {'R001', 'R002'}
sources = []
for p in graph['propositions']:
    if p['kind'] != 'external': continue
    s = p['source']; review = audit['source_reviews'][p['id']]
    sources.append({'id': p['id'], 'title': s['title'], 'author': s['author'], 'identifier': s['identifier'],
                    'version': s['version'], 'locator': s['locator'], 'verdict': review['verdict'],
                    'citation_checks': {k: v['verdict'] for k, v in review['citation_checks'].items()},
                    'primary_evidence': s['primary_evidence']})

summary = {
    'schema': 'benchmark-owner-terminal-metrics-1', 'method': 'Read exact canonical stage_history bindings and graph JSON; do not read copied evidence as new stages. No model, compiler, probe or re-review is launched.',
    'read_only_builtin_metrics_failure': {'status': 'VALIDATION_FAILED', 'exit_code': metrics_failure['exit_code'],
        'cause': "KeyError: 'request_number'", 'evidence': str(PROV/'terminal-validation/metrics.json'),
        'effect': 'Built-in wall/tool/request aggregation failed. The following direct stage metadata summary does not repair or relabel that command.'},
    'graphs': graphs, 'phase_times': phase_times, 'stages': stages, 'local_R_work_distribution': work,
    'case_elapsed_seconds': result['elapsed_case_seconds'],
    'dispatch_to_finalized_seconds': (dt(status['updated_at_utc'])-dt(launch['started_at_utc'])).total_seconds(),
    'started_at_utc': launch['started_at_utc'], 'finalized_at_utc': status['updated_at_utc'],
    'stage_count': len(stages), 'unique_native_threads': len({r['native_thread_id'] for r in stages}),
    'observed_peak_local_model_stages': case['concurrency']['audit_r']['observed_peak_model_stages'],
    'configured_local_workers': 20,
    'revisions': {'global_author_stages': 2, 'global_author_repairs': 1, 'global_A_stages': 2,
        'local_review_stages': 17, 'local_author_stages': 4, 'local_inference_patch_stages': 3,
        'located_global_escalations': 1, 'global_fallbacks': 1, 'epochs': 2,
        'explicit_reset_or_cold_rerun': 0,
        'definition': 'Counts are actual canonical stages/accepted artifact types, not a guessed number of mathematical proof changes. Global fallback follows the located GLOBAL_REPAIR_REQUIRED artifact; old judgments and costs are preserved.'},
    'known_native_faults': faults, 'controller_remote_retries': sum(r['remote_retries'] for r in stages),
    'error_pause_count': sum(len(r['error_pauses']) for r in stages), 'recorded_lean_calls': 0,
    'usage': {'status': 'PARTIAL', 'observed_tokens': tokens, 'matched_canonical_stage_ledgers': len(stages),
        'missing_stage_ledgers': [], 'requests': None, 'provider_response_coverage': None, 'actual_model_routing': 'UNVERIFIED',
        'observed_service_tier': 'UNVERIFIED', 'cached_and_reasoning_are_subsets': True,
        'owner_operator_overhead_included': False},
    'sources': sources, 'source_warnings': check['source_warnings'],
    'timing_qualification': 'All wall intervals include tools, service/network waits and repairs; parallel stage durations must not be added as case elapsed time. This run alone makes no comparative or isolated-speed claim.',
}
write_new(PROV/'terminal-metrics.json', summary)
write_new(PROV/'terminal-reading-disclosure.json', {'schema':'benchmark-owner-terminal-reading-disclosure-1',
    'read_json_files': sorted(READS), 'read_rules_or_code':['runtime/nl0/scripts/phase_metrics.py', 'runtime/nl0/scripts/nl0_review_loop.py'],
    'additional_observations': ['One terminal scheduled yui.py observe only; no new observation/poll loop during finalization.',
       'Final source target/source verdicts and per-R verdicts were read after termination; node counts use JSON fields, not a new mathematical re-audit.',
       'Stage result/native fault metadata and current bindings inspected; copied review-evidence is not counted as new execution.'],
    'deliberately_unread':['sealed/ directory and payload','parent/sibling chats or runs','historical proof/audit/source caches'],
    'write_exception': [str(ROOT), str(PACKET/'return')], 'seal_opened_or_enumerated':False})
validation_summary = {k:v for k,v in check.items() if k not in ['background_notes','background_supplement','topological_propositions']}
outcome = {
    'schema':'benchmark-owner-final-outcome-1','recorded_at_utc':datetime.now(timezone.utc).isoformat(),
    'run':str(ROOT),'job_id':job['id'],'handoff_id':state['handoff_id'],'owner_thread_id':state['owner_thread_id'],
    'track':'nl0','policy':'normal','profile':job['profiles']['nl0'],'max_concurrency':20,
    'mathematical_acceptance':{'status':result['status'],'scope':result['acceptance_scope'],'completion':result['completion'],
        'validation':validation_summary,'source':source,'authority':'Actual split global/per-R natural-language Audit A relative to explicit H/E and 45 reviewed background notes; the owner only validates bound artifacts. No Lean/formal certification.'},
    'source_qualification':{'conditional':False,'primary_source_warnings':[],'external_theorem_count':5,
        'source_review_status':'All 5 x 5 citation checks are PASS in the validated bound audit; external theorem proofs are not reproved by this run.','sources':sources},
    'execution_health':{'status':'COMPLETED_WITH_RECORDED_NATIVE_FAULT','native_faults':faults,
        'python_remote_retries':summary['controller_remote_retries'],'pause_count':summary['error_pause_count'],
        'benchmark_fault_free':False,'post_run_metrics_command_status':'VALIDATION_FAILED',
        'post_run_metrics_cause':"KeyError: 'request_number'"},
    'measurement':{**summary['usage'],'complete':False,'valid_as_complete_fault_free_benchmark':False},
    'metrics':summary,'process_exit':{'status':'CONFIRMED_NO_OWNED_PROCESSES','terminal_observation':observation,
        'recorded_process_identities':status['processes'],'case_controller':status['controller'],
        'batch_children_exited':batch['children_exited'],'no_authorized_recovery_pending':True},
    'monitor':{'automation_id':state['automation_id'],'heartbeat_deleted':False,'deletion_status':'PENDING_REPORT_SAVE'},
    'scope_compliance':{'full_to_nl0_override':preflight['scope_override'],'only_this_run_read':True,
        'sealed_payload_read_or_enumerated':False,'new_model_or_Lean_run_by_owner_at_termination':False,
        'translation_interfaces_Lean_proofs_assembly_Audit_B':'NOT_RUN_OUT_OF_SCOPE',
        'source_runtime_manifest':preflight['runtime'],'inherited_audit_evidence':'Only within this run, exact own prior reviewed scopes with provenance; no cross-run inputs.'},
    'final_report':str(ROOT/'FINAL_REPORT.zh.md'),'packet_returns':[str(PACKET/'return/first-pass.md'),str(PACKET/'return/receipt.md')],
}
write_new(ROOT/'FINAL_OUTCOME.json', outcome)

report = [f'# 本轮 NL0 + Audit A 最终报告\n\nmaster，本轮 **DRAFT-AUDIT-PASSED**，已用本轮冻结 validator 核验绑定验收。验收范围仅为自然语言 NL0 与独立 Audit A，结果相对五项显式外部定理及 45 条已审查 background notes。所有拥有进程及进程组均已确认退出。\n\nRun：`{ROOT}`\n\n模型请求/本地配置：gpt-6.1-sol / high / Standard，无 fallback；20 个局部 worker 上限，实际局部 model-stage 峰值 12。Provider 实际 routing/tier 未暴露，保持 UNVERIFIED。\n\n启动至最终状态：{local_time(summary["started_at_utc"])} 至 {local_time(summary["finalized_at_utc"])}（Asia/Shanghai），{summary["dispatch_to_finalized_seconds"]:.3f} 秒。原生 case elapsed 为 {result["elapsed_case_seconds"]:.3f} 秒。\n\n## 验收与来源\n\n冻结 validator 返回 current_standard_receipt_valid=true、audit_receipt_valid=true、independent_review_accepted=true；12 个 R 与完整 target 均通过，未解决审查项为空。源文件及完整 target-selection 字节绑定保持一致。5 个 E 各有 5 项 citation checks，全部为 PASS，无条件来源 warn。此处报告本轮实际审查与字节核验，不重新认证外部文献证明。\n\n未进入 translation preparation、接口、Lean 证明、组装或 Audit B；本轮所有阶段记录的 lean_calls 合计为 0。审查角色与作者分离，返修可保留自身先前 findings；恢复的全局角色有实际新 carrier 与显式 own-history，不能把每一次修订都称为全新上下文。\n\n## 初版与终版规模\n\n| 版本 | N | R | S | F |\n| --- | ---: | ---: | ---: | ---: |']
for name, g in zip(['首个结构验收作者稿','首轮局部合并','全局修订稿','最终验收稿'], graphs):
    report.append(f'| {name} | {g["N"]} | {g["R"]} | {g["S"]} | {g["F"]} |')
report.append('\nN 仅计 internal 命题，P 单列；S 为全部 argument 段落，F 为各段 produces 的局部事实记录总数。最终另有 H=3、E=5、P=1、D='+str(len(spec['definitions']))+'。45 条审核补充 background notes 不混入 F。\n\n## 阶段时间\n\n| 阶段 | 时间跨度（秒） | 阶段记录 wall_seconds 之和（秒） |\n| --- | ---: | ---: |')
phase_names=['初版 NL0','首轮 global A','首轮 local A 与局部返修','恢复全局作者修订','第二轮 global A','第二轮 local A 与局部返修']
for name, time in zip(phase_names, phase_times.values()):
    report.append(f'| {name} | {time["timestamp_span_seconds"]:.3f} | {time["sum_recorded_stage_wall_seconds"]:.3f} |')
report.append('\n跨度来自现有 start/finish 时间，包含组内阶段间隔；wall_seconds 是原始阶段字段，可因并行而重叠，也不包含所有外层初始化。两列均包含工具/网络等待，不能解释为纯推理时间，不能将并行阶段相加为全程时间。\n\n## 局部 R 工作分布\n\n| R | S/F | 审查次数 | 局部作者次数 | 审查累计秒 | 局部作者累计秒 | 观测 total tokens |\n| --- | ---: | ---: | ---: | ---: | ---: | ---: |')
for w in work:
    report.append(f'| {w["id"]} | {w["S"]}/{w["F"]} | {w["review_stages"]} | {w["repair_stages"]} | {w["review_wall_sum_seconds"]:.3f} | {w["repair_wall_sum_seconds"]:.3f} | {w["observed_total_tokens"]:,} |')
report.append(f'\n保留 {len(stages)} 个实际阶段、18 个不同 native thread。17 次局部审查；4 次局部作者阶段中 3 次提交 own-R patch，1 次返回 GLOBAL_REPAIR_REQUIRED，触发 1 次全局回退、1 次全局作者修订与第二轮审查。首轮 R001、R002 存在 nonpass，其他十项首审通过；终版 12 项全部通过。初版作者有 20 个候选/check，恢复全局作者有 5 个候选/check，这些是结构候选数，不等于独立数学修订数。原始 findings 与成本均保留，无额外 cold experiment。\n\n## 执行健康与用量限制\n\n一次已记录原生 provider 网络错误位于 audit-a/0001-0001/global/stage/result.json：Reconnecting... waiting for network / responseStreamDisconnected / Connection failed: error sending request，native_will_retry=true。该原始 stage 的 execution_health=FAULT、execution_qualified=false 保持不变；Python controller 的 remote_retries 合计为 0，没有 PAUSED_ERROR。最终绑定验收有效不抹去这次执行故障，不能把本轮当作全程无故障 benchmark。\n\n内置只读 yui.py metrics 命令为 VALIDATION_FAILED：phase_metrics.py 对原生 request-lifecycle 读取 request_number 时抛出 KeyError。错误原样保存在 owner-provenance/terminal-validation/metrics.json，未修改运行时。此报告从 canonical stage_history 的 25 个绑定 result/usage 与图 JSON 直接汇总，算法保存在 owner-provenance/finalize_report.py；没有以汇总替代失败命令的状态。\n\n观测 input={tokens["input_tokens"]:,}、output={tokens["output_tokens"]:,}、total={tokens["total_tokens"]:,}。cached input={tokens["cached_input_tokens"]:,} 属于 input 子集；reasoning={tokens["reasoning_tokens"]:,} 属于 output 子集，均不另行相加。25 个 canonical stage ledger 与 case 总计精确对齐，无 missing ledger；provider 逐响应覆盖、请求数及 actual tier 仍未知，因此 usage=PARTIAL、measurement_complete=false。Owner 操作开销不计入以上 worker 用量。\n\n## 范围与返回\n\n共享配置中的 full 已由本次明确授权覆盖为 nl0；安装代码、提示词、分支、settings.json 与 .prepared 均未修改。冻结 runtime 包含启动时既有未提交改动，按实际 manifest 绑定，不能只用 Git commit 判定版本。未读取父/兄弟 chat、历史或其他 run，未读取或枚举 sealed/，无运行间比较。OWNER_MONITOR_LOG.jsonl 含真实有界观察；终态观察已确认无拥有进程/进程组，无待授权恢复。heartbeat 将在本报告与回执保存后删除，真实删除回执另存 owner-provenance/monitor-removal.json。\n\n详细机器结果：FINAL_OUTCOME.json；直接汇总：owner-provenance/terminal-metrics.json；完整 validator 输出：owner-provenance/terminal-validation/audit-a-check.json；终态读取声明：owner-provenance/terminal-reading-disclosure.json。\n\n操作返回：交接包 return/first-pass.md 与 return/receipt.md；封印保持关闭。')
(ROOT/'FINAL_REPORT.zh.md').write_text('\n'.join(report)+'\n')

first = f'''# 本轮首版记录\n\n## Control\n\nmaster，按本包一次 normal / nl0 / gpt-6.1-sol / high / Standard / 20 workers 的授权执行。首版是本轮冷启动作者产生的首个结构验收稿，未读取旧结论或 sibling。\n\n## Target Preservation\n\n完整冻结目标与本包原始目标字节一致。启动前对原始 PDF 第 2、3 页做图文核对。首版目标保留全定理、固定 scheme 与量词；来源/目标语义最终由实际 Audit A 核验。\n\n## Result\n\n首版 N/R/S/F=11/12/43/30，路径 `{graphs[0]['path']}`。首版作者 wall_seconds={stages[0]['wall_seconds']:.3f}；start/finish 跨度={phase_times['initial_NL0']['timestamp_span_seconds']:.3f} 秒。首个全局 gate accepted=true、conditional=false、complete=true；首轮 R001 与 R002 nonpass，其他十项首审 PASS，不能将首个全局 gate 或结构验收当作首版整个 Audit A 通过。此后保留正常局部返修与一次全局回退，终版另见 FINAL_OUTCOME.json。\n\n## Return Contract\n\n本记录只描述本轮首版，不与历史或另一重复比较。最终状态、故障、量度限制及进程退出证据见本轮最终报告；数学范围只有 NL0 + Audit A。\n\n## Disclosure Compliance\n\n已读与故意未读清单见 `{PROV/'owner-reading-disclosure.json'}` 与 `{PROV/'terminal-reading-disclosure.json'}`。仅在终态后读本轮 canonical 图、审查 verdict 与阶段元数据用于核验/统计；sealed/ 未读取或枚举。写入只在本包 return/、本轮 run 与 native runtime 登记隔离 sandbox 的明确例外范围。\n\n## Cross-Agent Provenance\n\n操作拥有者 Codex，owner chat {state['owner_thread_id']}；owner 实际模型/effort 未由已用工具暴露，保持 UNVERIFIED。SAME_VENDOR_FRESH_CONTEXT 为独立新 task 的上下文自述，不是技术强制隔离或跨厂商证明。实际测量配置由 native receipts 记录；首版作者和全局/局部审查角色分离，返修保留自身会话历史。操作启动、哈希/进程检查为 observed；未读取 seal 与未提供额外数学提示为 owner 行为自述，不能混同为审查数学正确性证书。\n'''
(PACKET/'return/first-pass.md').write_text(first)
receipt = f'''# 本轮独立操作最终回执\n\n## Control\n\nmaster，本包唯一 run `{ROOT}` 已到 DRAFT-AUDIT-PASSED 终态。范围 nl0、normal、gpt-6.1-sol/high/Standard、20 worker，无额外 case/stage/token/call 限额；共享 full 默认的覆盖已经写入启动和最终 provenance。已确认本轮拥有 PID/start/PGID 及进程组全部退出，无 pending recovery。heartbeat ID yui-nl0-01 将在报告保存后删除，真实回执随 FINAL_OUTCOME.json 更新。没有重启、另开实验或 owner 模型/Lean 核验运行。\n\n## Target Preservation\n\n使用原始 PDF 与本包完整 target-selection；原文目标核对、文件绑定、spec full_target 等值、最终 target/graph/source 审查均有实际记录。保留 T>0、0<gamma<=1、R>0、整个初值球统一常数、所有许可步长、完整无 cutoff 固定 scheme。没有从旧 proof 或 sealed 材料填入结果。\n\n## Result\n\n绑定 current-standard Audit A receipt 已用本轮 frozen validator 核验通过：12 R、5 E、45 background notes，source warnings 为空；自然语言数学审查相对显式外部前提，未声称 Lean/formal certification。初版 N/R/S/F=11/12/43/30，最终=11/12/45/32。case elapsed={result['elapsed_case_seconds']:.3f} 秒；dispatch 至 finalized={summary['dispatch_to_finalized_seconds']:.3f} 秒。\n\n执行健康为 COMPLETED_WITH_RECORDED_NATIVE_FAULT：首个 global A 一次 native disconnect，原始 execution_qualified=false 保留；只读 metrics 命令 VALIDATION_FAILED（KeyError: request_number）。用量 PARTIAL：input {tokens['input_tokens']:,}、output {tokens['output_tokens']:,}、total {tokens['total_tokens']:,}；cached/reasoning 是子集。25 项 stage ledger 对齐不等于逐 provider 响应覆盖完整，actual routing/tier 未验证。\n\n## Return Contract\n\n结果、来源资格、执行健康与量度完整性分开报告。主产物为 FINAL_OUTCOME.json、FINAL_REPORT.zh.md、nl0/merged-0002/{{spec.json,nl0.json,audit-a.json}}、owner-provenance/terminal-validation/ 与 terminal-metrics.json。初版、阶段时间、局部 R 分布、返修/回退和 native fault 全部仅描述本轮；没有读 sibling 或历史基线作比较。\n\n## Disclosure Compliance\n\n启动已读逐项清单在 owner-provenance/owner-reading-disclosure.json；终态已读路径在 terminal-reading-disclosure.json。另读本轮阶段 result/accepted、全局 gate、graph/spec/audit、源选择、batch/process/status 与 frozen validator/汇总代码；runtime 文件和输入做 hash 绑定验证。故意不读：sealed/ 内容与目录、父/兄弟 chat、其他结果/旧审查/问题日志/来源缓存。\n\n实际写入：本包 return/ 启动/图文核对/首版/最终回执；本轮 root 的 job/inputs/runtime/native stages/OWNER_MONITOR_STATE.json/OWNER_MONITOR_LOG.jsonl/FINAL_OUTCOME.json/FINAL_REPORT.zh.md/owner-provenance；临时隔离资源仅由 Yui native runtime 创建登记与释放。后两类写入是交接包明确允许的运行结果与隔离 OS 资源例外，未扩大为共享代码或配置修改。写入索引见 OWNER_WRITE_PATHS.json。\n\n## Cross-Agent Provenance\n\n操作 owner：Codex /root，chat {state['owner_thread_id']}；当前 owner 模型和 profile 不由已用工具暴露，保持 UNVERIFIED。上下文新 task 为 SAME_VENDOR_FRESH_CONTEXT 自述，不声称跨厂商或技术强制隔离；全局记忆未转交测量模型。\n\nObserved：registry/preparation 结果、冻结输入/runtime hashes、执行命令、controller PID/start/PGID、实际 automation ID、terminal process/group exits、validator 返回、canonical stage metadata、明确数学 verdict 与用量计数。Self-attested：owner 没有主动读 seal/历史/sibling、没有向 worker 添加数学提示；该行为声明不能替代技术证据。Native role 由每项 exposure/native thread/role_session receipts 描述：本地 identity/input boundary 检查通过，作者与审查角色分离，反复审查保留自己历史；provider payload、actual model routing 与 tier 未暴露。原始故障 stage 的 qualification 不因最终验收而改写。\n'''
(PACKET/'return/receipt.md').write_text(receipt)
files = sorted(str(p) for p in ROOT.rglob('*') if p.is_file())
write_new(ROOT/'OWNER_WRITE_PATHS.json', {'schema':'benchmark-owner-write-paths-1','scope':'This run inventory after terminal reports; copied runtime files are runtime snapshots, not edits to shared originals.',
    'run_root':str(ROOT),'run_files':files,'packet_return_files':sorted(str(p) for p in (PACKET/'return').iterdir() if p.is_file()),
    'native_sandboxes':'Exact ephemeral workspace ownership/release receipts remain under each stage/resources; released resources are not scientific-run deletion.',
    'late_monitor_deletion_receipt':str(PROV/'monitor-removal.json')})
print(json.dumps({'status':'FINAL_REPORTS_SAVED','mathematical_status':result['status'],'case_seconds':result['elapsed_case_seconds'],
    'first_N_R_S_F':{k:graphs[0][k] for k in ['N','R','S','F']},'final_N_R_S_F':{k:graphs[-1][k] for k in ['N','R','S','F']},
    'phase_times':phase_times,'usage':summary['usage'],'fault_count':len(faults),'return_files':[str(PACKET/'return/first-pass.md'),str(PACKET/'return/receipt.md')],
    'next_action':'Delete actual heartbeat after report-save checks; append real deletion receipt and update monitor status.'},ensure_ascii=False,indent=2))
