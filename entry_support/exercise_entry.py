"""Single-problem entry around the installed Yui CLI; never a proof solver."""
from __future__ import annotations

import argparse
from datetime import datetime,timezone
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import uuid

from common import digest,local,write,json_call,runtime_call,support_bindings,CAPABILITY_CHECK,terminal_check,terminal_ready
from skill_check import require_skill
from owner_monitor import record_monitor,validate_monitor


def utc():return datetime.now(timezone.utc).isoformat()


def runtime_binding(root, *, public_workflow=False):
    root=Path(root);rows={}
    names=('SKILL.md','config.json','nl0','nl02lean','toolchain')
    if public_workflow:
        names+=('workflow',)
    for name in names:
        base=root/name
        for path in [base] if base.is_file() else base.rglob('*'):
            if path.is_file() and '__pycache__' not in path.parts and (path.suffix in {'.py','.json','.md','.lean','.mjs'} or path==root/'workflow/requirements.txt'):
                rows[str(path.relative_to(root))]=digest(path)
    import hashlib
    return hashlib.sha256(json.dumps(rows,sort_keys=True).encode()).hexdigest()


def verify_revision(root, expected):
    root=Path(root).resolve()
    def git(*args):
        return subprocess.check_output(['git','-C',str(root),*args],text=True,stderr=subprocess.PIPE).strip()

    if Path(git('rev-parse','--show-toplevel')).resolve()!=root:
        raise ValueError('The registered Yui installation must be the pinned checkout')
    actual={'branch':git('rev-parse','--abbrev-ref','HEAD'),'commit':git('rev-parse','HEAD')}
    if actual!=expected:
        raise ValueError(f'Registered Yui revision {actual} differs from the requested {expected}')
    if git('status','--porcelain','--untracked-files=normal','--',
           'SKILL.md','config.json','nl0','nl02lean','toolchain','library','workflow'):
        raise ValueError('The registered Yui checkout has unpublished runtime changes')
    return actual


def target_section(text,heading):
    lines=text.splitlines(keepends=True);starts=[i for i,line in enumerate(lines) if line.rstrip()==heading]
    if len(starts)!=1:raise ValueError('Expected exactly one configured complete-target heading')
    start=starts[0]+1;end=next((i for i in range(start,len(lines)) if lines[i].startswith('## ')),len(lines))
    body=''.join(lines[start:end]).strip()
    if not body:raise ValueError('The complete-target section is empty')
    return body,start+1,end


class Entry:
    def __init__(self,root):self.root=Path(root).resolve()

    def config(self):
        c=json.loads(local(self.root,'settings.json').read_text())
        fields={'schema','case_id','input','input_sha256','target_heading','formalization','track','policy',
            'profiles','results_directory','limits','monitor'}
        if self.root.parent.name=='test_uncond':
            fields.add('yui_revision')
        if not isinstance(c, dict) or set(c) - {'workers'} != fields or c['schema'] != 'yui-exercise-entry-1':
            raise ValueError('Unknown exercise settings')
        if 'yui_revision' in c:
            pin=c['yui_revision']
            if (not isinstance(pin,dict) or set(pin)!={'branch','commit'} or pin['branch']!='main'
                    or not isinstance(pin['commit'],str) or not re.fullmatch('[0-9a-f]{40}',pin['commit'])
                    or c['formalization']!='unconditional'):
                raise ValueError('The unconditional entry requires a pinned Yui main revision')
        if c['case_id']!=self.root.name or c['input']!='problem.md' or c['results_directory']!='rigorous-proof':raise ValueError('Wrong exercise identity or local paths')
        headings={'geometry-product-dimension':'## Fixed interpretation and complete target',
            'lie-module-irreducibility':'## Definitions and complete target','wave-map-energy':'## Fixed interpretation and complete target'}
        if c['target_heading']!=headings.get(c['case_id']):raise ValueError('Use the problem\'s complete target section')
        if c['formalization'] not in {'conditional','unconditional'} or c['track']!='full' or c['policy']!='normal':raise ValueError('Use an explicit full conditional/unconditional goal and normal policy')
        if not isinstance(c['input_sha256'],str) or not re.fullmatch('[0-9a-f]{64}',c['input_sha256']):raise ValueError('Bind the original problem bytes')
        if 'workers' in c and (type(c['workers']) is not int or c['workers'] < 1):
            raise ValueError('An explicit worker cap must be a positive integer')
        if set(c['profiles'])!={'nl0','lean'}:raise ValueError('Both phase profiles are required')
        for p in c['profiles'].values():
            if set(p)!={'id','reasoning_effort','speed','automatic_fallback'} or not all(isinstance(p[k],str) and p[k] for k in ('id','reasoning_effort','speed')) or p['automatic_fallback'] is not False:
                raise ValueError('Use complete explicit profiles without fallback')
        limits=c['limits']
        if (not isinstance(limits,dict) or set(limits)!={'case_seconds','stage_seconds','tokens','model_calls','native_seconds'}
                or any(limits[k] is not None for k in ('case_seconds','stage_seconds','tokens','model_calls'))
                or type(limits['native_seconds']) is not int or limits['native_seconds']<=0):
            raise ValueError('Keep unlimited total budgets and specify the native-call limit from the selected runtime')
        validate_monitor(c['monitor'])
        target_section(local(self.root,'problem.md').read_text(),c['target_heading'])
        return c

    def check(self,codex=None):
        c=self.config()
        if digest(local(self.root,c['input']))!=c['input_sha256']:raise ValueError('Problem changed; review and update its explicit input pin')
        installed=require_skill(cwd=self.root,codex=codex)
        revision=verify_revision(installed['root'],c['yui_revision']) if 'yui_revision' in c else None
        program='''import json,sys
from pathlib import Path
root=Path(sys.argv[1]);c=json.load(sys.stdin)
sys.path[:0]=[str(root/'nl0/scripts'),str(root/'nl02lean/scripts')]
from runtime_config import verify,native_timeout
from entrypoint import preflight_profiles
preflight_profiles({'track':'full','profiles':c['profiles']})
runtime=json.loads((root/'config.json').read_text())
if runtime['timeouts']!={k:c['limits'][k] for k in ('case_seconds','stage_seconds','native_seconds')} or runtime['token_budget'] is not None:
 raise ValueError('Installed runtime limits differ from this entry')
if native_timeout()!=c['limits']['native_seconds']:raise ValueError('Wrong native-call limit')
print(json.dumps({'environment':verify()}))
'''
        environment=runtime_call(installed['root'],program,data=c)
        capabilities=runtime_call(installed['root'],CAPABILITY_CHECK,c['formalization'])
        bindings={'startup':{n:digest(local(self.root,n)) for n in ('README.md','settings.json','run_test.py')},
            'support':support_bindings(),'input':c['input_sha256'],'runtime':runtime_binding(installed['root'],public_workflow=bool(revision)),
            'installed':{k:installed[k] for k in ('root','skill_md','skill_sha256')}}
        if revision:bindings['yui_revision']=revision
        return {'status':'ENVIRONMENT-CHECKED','configuration':c,'installed':installed,'bindings':bindings,
            'capabilities':capabilities,'environment':environment,'model_started':False}

    def owned(self,run):
        run=Path(run).absolute();base=local(self.root,'rigorous-proof')
        if '..' in run.parts or run.is_symlink() or run.parent.resolve()!=base.resolve() or not run.is_dir():raise ValueError('Select one current entry-owned run')
        r=json.loads(local(run,'TEST_RUN.json').read_text())
        if r.get('schema')!='yui-exercise-run-1' or r.get('run')!=str(run.resolve()) or r.get('entry')!=str(self.root):raise ValueError('Wrong/relocated run ownership')
        return run.resolve(),r

    def save(self,run,r,status,**changes):
        r.update(status=status,updated_at_utc=utc(),**changes);write(run/'TEST_RUN.json',r)

    def current(self,r):
        check=self.check()
        if check['configuration']!=r['configuration'] or check['bindings']!=r['bindings']:raise ValueError('Stale source/configuration/runtime; do not replace an active run')
        return check

    def begin(self,run_id=None,codex=None):
        started=utc();check=self.check(codex)
        identifier=run_id or datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:10]
        if not isinstance(identifier,str) or not re.fullmatch('[A-Za-z0-9][A-Za-z0-9._-]{0,99}',identifier):raise ValueError('Invalid fresh run ID')
        base=local(self.root,'rigorous-proof');base.mkdir(exist_ok=True)
        run=local(base,identifier);run.mkdir(exist_ok=False)
        r={'schema':'yui-exercise-run-1','entry':str(self.root),'run':str(run),'started_at_utc':started,
            **{k:check[k] for k in ('configuration','installed','bindings')},'model_started':False}
        self.save(run,r,'PREPARING_SOURCE')
        try:
            prep=run/'preparation';prep.mkdir();startup=prep/'startup';startup.mkdir()
            for name in r['bindings']['startup']:shutil.copyfile(self.root/name,startup/name)
            support=startup/'entry_support';support.mkdir()
            for name in r['bindings']['support']:shutil.copyfile(Path(__file__).parent/name,support/name)
            shutil.copyfile(local(self.root,'problem.md'),prep/'problem.md')
            statement,start,end=target_section((prep/'problem.md').read_text(),r['configuration']['target_heading'])
            (prep/'target-statement.md').write_text(statement+'\n')
            write(prep/'source-review.json',{'schema':'yui-exercise-readback-1','source_sha256':digest(prep/'problem.md'),
                'source_read':False,'target_checked':False,'source_only':False,'notes':''})
            self.save(run,r,'SOURCE_REVIEW_REQUIRED',target_lines=[start,end],source_sha256=digest(prep/'problem.md'),
                target_sha256=digest(prep/'target-statement.md'))
        except Exception as error:
            self.save(run,r,'PREPARATION_FAILED',error=str(error));raise
        return {'status':r['status'],'run':str(run),'model_started':False}

    def verify_inputs(self,run,r):
        prep=local(run,'preparation')
        if digest(local(prep,'problem.md'))!=r['source_sha256'] or digest(local(prep,'target-statement.md'))!=r['target_sha256']:
            raise ValueError('Frozen original source or complete target changed')
        for name,sha in r['bindings']['startup'].items():
            if digest(local(prep,'startup/'+name))!=sha:raise ValueError('Startup provenance changed')
        for name,sha in r['bindings']['support'].items():
            if digest(local(prep,'startup/entry_support/'+name))!=sha:raise ValueError('Shared adapter provenance changed')
        for key,name in [('review_sha256','source-review.json'),('selection_sha256','target-selection.json')]:
            if key in r and digest(local(prep,name))!=r[key]:raise ValueError('Reviewed input changed')

    def prepare(self,run):
        run,r=self.owned(run)
        if r['status']!='SOURCE_REVIEW_REQUIRED':raise ValueError('Prepare once after this run\'s source readback')
        self.current(r);self.verify_inputs(run,r);prep=run/'preparation';c=r['configuration']
        review=json.loads(local(prep,'source-review.json').read_text())
        if (set(review)!={'schema','source_sha256','source_read','target_checked','source_only','notes'} or
                review['schema']!='yui-exercise-readback-1' or review['source_sha256']!=r['source_sha256'] or
                any(review[k] is not True for k in ('source_read','target_checked','source_only')) or not isinstance(review['notes'],str)):
            raise ValueError('Complete the actual source-only readback and target check first')
        selection_program='''import json,sys
from pathlib import Path
root=Path(sys.argv[1]);prep=Path(sys.argv[2]);sys.path.insert(0,str(root/'nl0/scripts'))
from target_selection import select
print(json.dumps(select(prep/'problem.md',[{'id':'complete-target','label':'Complete configured target',
 'statement':(prep/'target-statement.md').read_text().strip(),'start_line':int(sys.argv[3]),'end_line':int(sys.argv[4])}],basis='current_run_fixed_target_section')))
'''
        selection=runtime_call(r['installed']['root'],selection_program,str(prep),*map(str,r['target_lines']))
        if selection.get('document')!={'path':str(prep/'problem.md'),'sha256':r['source_sha256']}:raise ValueError('Target selection refers to another source')
        write(prep/'target-selection.json',selection,exclusive=True)
        workflow=run/'workflow'
        args=[sys.executable,'-B',str(Path(r['installed']['root'])/'nl0/scripts/yui.py'),'prepare',str(prep/'problem.md'),
            '--track','full','--policy','normal',
            '--target-file',str(prep/'target-selection.json'),'--output',str(workflow)]
        if 'workers' in c:
            args.extend(['--max-concurrency', str(c['workers'])])
        if r['configuration']['formalization']=='unconditional' or r['installed'].get('unconditional_supported'):
            args+=['--formalization',c['formalization']]
        else:
            capabilities=runtime_call(r['installed']['root'],CAPABILITY_CHECK,c['formalization'])
            if capabilities['unconditional_supported']:args+=['--formalization',c['formalization']]
        for phase,p in c['profiles'].items():
            for flag,key in [('model','id'),('effort','reasoning_effort'),('speed','speed')]:args+=['--'+phase+'-'+flag,p[key]]
        write(run/'prepare-attempt.json',{'argv':args,'started_at_utc':utc()},exclusive=True)
        self.save(run,r,'PREPARING_JOB',review_sha256=digest(prep/'source-review.json'),selection_sha256=digest(prep/'target-selection.json'))
        try:
            result=json_call(args,log=run/'prepare-result.json')
            if result.get('status')!='PREPARED_NOT_STARTED' or result.get('runs')!=[str(workflow)]:raise ValueError('Unexpected prepared workflow')
            self.validate_job(run,r)
            self.save(run,r,'JOB_PREPARED',job_sha256=digest(workflow/'job.json'),
                frozen_runtime_sha256=runtime_binding(workflow/'runtime',public_workflow='yui_revision' in c))
        except Exception as error:self.save(run,r,'JOB_PREPARATION_FAILED',error=str(error));raise
        return {'status':r['status'],'run':str(run),'workflow':str(workflow),'model_started':False}

    def validate_job(self,run,r):
        w=run/'workflow';job=json.loads(local(w,'job.json').read_text());c=r['configuration'];prep=run/'preparation'
        if 'yui_revision' in c and (job.get('workflow_protocol')!='yui-workflow-1'
                or not local(w,'runtime/workflow/workflow.json').is_file()):
            raise ValueError('The prepared job lacks the frozen public Yui workflow')
        expected={'root':str(w),'problem':str(prep/'problem.md'),'track':'full','policy':'normal','profiles':c['profiles'],
            'max_concurrency':c.get('workers', 'auto'),'source':None,'audit':None,'time_budget_seconds':None}
        if any(job.get(k)!=v for k,v in expected.items()) or job.get('formalization','conditional')!=c['formalization'] or 'resume' in job:
            raise ValueError('Prepared job changed goal, inputs or configuration')
        selection=json.loads((prep/'target-selection.json').read_text())
        if job.get('target_selection')!=selection:raise ValueError('Prepared job changed the complete target')
        docs=job.get('documents',[])
        if len(docs)!=2 or {d.get('id') for d in docs}!={'problem.md','target-selection.json'}:raise ValueError('Unexpected/historical construction inputs')
        for d in docs:
            name=d['id'];path=local(w,'inputs/'+name)
            if d.get('path')!=name or digest(path)!=d['sha256'] or d.get('original')!={'path':str(prep/'problem.md'),'sha256':r['source_sha256']}:
                raise ValueError('Unbound or changed job input')
        if (w/'inputs/problem.md').read_bytes()!=(prep/'problem.md').read_bytes() or json.loads((w/'inputs/target-selection.json').read_text())!=selection:
            raise ValueError('Current source bytes changed')
        return job

    def frozen(self,run,r):
        root=local(run,'workflow/runtime')
        if runtime_binding(root,public_workflow='yui_revision' in r['configuration'])!=r['frozen_runtime_sha256']:
            raise ValueError('Frozen runtime changed')
        return root

    def launch(self,run,*,heartbeat_id=None):
        run,r=self.owned(run)
        if r['status']!='JOB_PREPARED':raise ValueError('Dispatch once from JOB_PREPARED; inspect an old attempt, never repeat it')
        self.current(r);self.verify_inputs(run,r);self.validate_job(run,r)
        if digest(local(run,'workflow/job.json'))!=r['job_sha256']:raise ValueError('Prepared job changed')
        args=[sys.executable,'-B',str(self.frozen(run,r)/'nl0/scripts/yui.py'),'execute',str(run/'workflow'),'--detach']
        monitor = record_monitor(heartbeat_id, run, self.root/'run_test.py', r['configuration']['monitor'], write=write)
        write(run/'dispatch-attempt.json',{'argv':args,'started_at_utc':utc()},exclusive=True)
        self.save(run,r,'DISPATCHING',launch_started_at_utc=utc())
        try:
            result=json_call(args,log=run/'dispatch-result.json')
            who=result.get('controller',{})
            if result.get('status')!='DISPATCHED' or result.get('runs')!=[str(run/'workflow')] or not all(who.get(k) is not None for k in ('pid','pgid','started')):
                raise ValueError('Unverified dispatch; inspect actual owned processes')
            self.save(run,r,'DISPATCHED',model_started=None)
            result['owner_observation'] = {**result.get('owner_observation', {}), **monitor}
            return result
        except Exception as error:self.save(run,r,'DISPATCH_ERROR',error=str(error));raise

    def action(self,run,action):
        run,r=self.owned(run)
        if action=='cancel' and not (run/'dispatch-attempt.json').exists():
            self.save(run,r,'CANCELLED_PREPARATION');return {'status':'CANCELLED_PREPARATION','run':str(run)}
        if action not in {'observe','cancel'}:raise ValueError('Unknown action')
        result=json_call([sys.executable,'-B',str(self.frozen(run,r)/'nl0/scripts/yui.py'),action,str(run/'workflow')],timeout=60)
        if action=='observe':
            cases=result.get('cases',[])
            if len(cases)!=1 or cases[0].get('run')!=str(run/'workflow'):raise ValueError('Observation belongs to another workflow')
            with local(run,'OWNER_MONITOR_LOG.jsonl').open('a') as stream:stream.write(json.dumps({'at_utc':utc(),'observation':result})+'\n')
        return result

    def finish(self,run):
        run,r=self.owned(run)
        if (run/'FINAL_OUTCOME.json').exists():raise ValueError('Preserve the existing final report')
        self.verify_inputs(run,r);self.validate_job(run,r)
        snapshot=self.action(run,'observe')
        if not terminal_ready(snapshot):
            raise ValueError('Workflow is live, paused or its process exit is unverified')
        row=snapshot['cases'][0]
        if row.get('paused_errors')!=[] or row.get('live_owned_process_count')!=0 or row.get('registered_groups_still_present')!=[]:
            raise ValueError('Retained errors or processes remain')
        w=run/'workflow';case=json.loads(local(w,'case-result.json').read_text())
        if case.get('job')!={'path':str(w/'job.json'),'sha256':digest(w/'job.json')} or digest(w/'job.json')!=r['job_sha256']:raise ValueError('Unbound final result')
        from resource_cleanup import TERMINAL_OUTCOMES
        if case['result']['status'] not in TERMINAL_OUTCOMES:
            raise ValueError('Nonterminal case result cannot be finalized')
        if row.get('recorded_result') is not None and row['recorded_result']!=case['result']['status']:
            raise ValueError('Terminal observation disagrees with the bound case result')
        validation=terminal_check(self.frozen(run,r),w,r['configuration']['formalization'])
        result=case['result'];end=datetime.fromtimestamp((w/'case-result.json').stat().st_mtime,timezone.utc)
        final={'schema':'yui-exercise-final-1','run':str(run),'status':result['status'],'configuration':r['configuration'],
            'validation':validation,'result':result,'process_exit':snapshot,
            'timing':{'started_at_utc':r['started_at_utc'],'terminal_at_utc':end.isoformat(),
                'total_seconds':(end-datetime.fromisoformat(r['started_at_utc'])).total_seconds(),
                'case_seconds':result.get('elapsed_case_seconds'),'closed_at_utc':utc()}}
        write(run/'FINAL_OUTCOME.json',final,exclusive=True)
        report=f"# 测试结果\n\n状态：`{result['status']}`\n\n要求：`{r['configuration']['formalization']}`；题目：`{r['configuration']['case_id']}`。\n\n"
        report+='审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。\n\n'
        report+='耗时与 token 覆盖：\n\n```json\n'+json.dumps({'timing':final['timing'],'usage':result.get('usage'),'warnings':result.get('warnings'),
            'closure':result.get('closure')},ensure_ascii=False,indent=2)+'\n```\n'
        (run/'FINAL_REPORT.zh.md').write_text(report)
        self.save(run,r,'FINALIZED');return final

    def cleanup(self,run):
        run,r=self.owned(run)
        if not (run/'workflow/case-result.json').exists():raise ValueError('No actual terminal result; keep active resources')
        self.verify_inputs(run,r)
        self.validate_job(run,r)
        if digest(local(run,'workflow/job.json'))!=r['job_sha256']:raise ValueError('Prepared job changed')
        cleanup_file=local(run,'preparation/startup/entry_support/resource_cleanup.py')
        terminal_check(self.frozen(run,r),run/'workflow',r['configuration']['formalization'])
        try:
            result=json_call([sys.executable,'-B',cleanup_file,str(run/'workflow'),str(self.frozen(run,r))])
        except Exception as error:
            write(run/'CLEANUP.json',{'status':'CLEANUP_BLOCKED','error':str(error)});raise
        terminal_check(self.frozen(run,r),run/'workflow',r['configuration']['formalization'])
        write(run/'CLEANUP.json',result);return result


def main(root,argv=None):
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('command',choices=['check','begin','prepare','launch','observe','cancel','finish','cleanup'])
    parser.add_argument('run',type=Path,nargs='?');parser.add_argument('--codex',type=Path);parser.add_argument('--run-id')
    parser.add_argument('--heartbeat-id', help='Optional existing permitted host heartbeat ID; omit for in-chat waiting')
    args=parser.parse_args(argv);entry=Entry(root)
    try:
        if args.command=='check':result=entry.check(args.codex)
        elif args.command=='begin':result=entry.begin(args.run_id,args.codex)
        elif args.run is None:raise ValueError('Select the exact run returned by begin')
        elif args.command in {'observe','cancel'}:result=entry.action(args.run,args.command)
        elif args.command=='launch':result=entry.launch(args.run,heartbeat_id=args.heartbeat_id)
        else:result=getattr(entry,args.command)(args.run)
        print(json.dumps(result,ensure_ascii=False,indent=2));return 0
    except (OSError,ValueError,KeyError,TypeError,subprocess.SubprocessError) as error:
        print(json.dumps({'status':'ENTRY_ACTION_BLOCKED','action':args.command,'error':str(error)},ensure_ascii=False,indent=2));return 1
