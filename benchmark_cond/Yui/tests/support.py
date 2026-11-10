"""Synthetic metadata/PDF/runtime fixtures. Never calls a real model or Lean."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

BENCHMARK = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCHMARK))
import benchmark_config
import prepare_yui
import skill_check

REQUIRED = ['config.json', 'nl0/scripts/yui.py', 'nl0/scripts/entrypoint.py',
            'nl0/scripts/target_selection.py', 'nl0/scripts/nl0.py',
            'nl02lean/scripts/workflow.py', 'nl02lean/scripts/final_acceptance.py',
            'toolchain/lock.json']

FAKE_YUI = r'''import argparse,hashlib,json,os,shutil,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
mode=os.environ.get('YUI_TEST_MODE','')
def write(p,v):p.write_text(json.dumps(v))
def binding(p):return {'path':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
with open(os.environ['YUI_TEST_CALLS'],'a') as out:out.write(json.dumps(sys.argv[1:])+'\n')
a=sys.argv[1:];cmd=a[0]
if cmd=='prepare':
 if mode=='prepare_exit':print('synthetic preparation failure',file=sys.stderr);raise SystemExit(7)
 if mode=='bad_json':print('not JSON');raise SystemExit(0)
 if mode=='json_list':print('[]');raise SystemExit(0)
 p=argparse.ArgumentParser();p.add_argument('problem',type=Path)
 p.add_argument('--max-concurrency', default='auto')
 for name in ('track','policy','target-file','output'):
  p.add_argument('--'+name,required=True)
 p.add_argument('--material')
 p.add_argument('--formalization',default='conditional')
 for phase in ('nl0','lean'):
  for name in ('model','effort','speed'):p.add_argument('--'+phase+'-'+name,required=True)
 v=p.parse_args(a[1:]);w=Path(v.output);w.mkdir();(w/'inputs').mkdir()
 profiles={phase:{'id':getattr(v,phase+'_model'),'reasoning_effort':getattr(v,phase+'_effort'),'speed':getattr(v,phase+'_speed'),'automatic_fallback':False} for phase in ('nl0','lean')}
 if v.track=='nl0':profiles['lean']=dict(profiles['nl0'])
 docs=[]
 selection=json.loads(Path(v.target_file).read_text())
 inputs=[('problem.md',v.problem,b'synthetic full paper' if v.problem.suffix=='.pdf' else v.problem.read_bytes())]
 if v.material:inputs.append(('material-001.md',Path(v.material),Path(v.material).read_bytes()))
 inputs.append(('target-selection.json',v.problem,Path(v.target_file).read_bytes()))
 for name,source,data in inputs:
  dest=w/'inputs'/name;dest.write_bytes(data);docs.append({'id':name,'path':name,'sha256':binding(dest)['sha256'],'original':binding(source),'extraction':'synthetic'})
 max_concurrency = 'auto' if v.max_concurrency == 'auto' else int(v.max_concurrency)
 job={'formalization':v.formalization,'root':str(w),'problem':str(v.problem),'track':v.track,'policy':v.policy,'profiles':profiles,'max_concurrency':max_concurrency,'source':None,'audit':None,'time_budget_seconds':None,'documents':docs,'target_selection':selection}
 if mode=='extra_input':job['documents'].append({'id':'prior.md'})
 if mode=='wrong_formalization':job['formalization']='conditional' if v.formalization=='unconditional' else 'unconditional'
 if mode=='wrong_track':job['track']='full' if v.track=='nl0' else 'nl0'
 if mode=='wrong_workers':job['max_concurrency']=1
 if mode=='wrong_profile':job['profiles']['nl0']['id']='unrequested'
 if mode=='wrong_root':job['root']=str(w.parent.parent/'another-run')
 if mode=='resume':job['resume']={'prior':'old-result'}
 if mode=='wrong_target':job['target_selection']={**selection,'full_target':'wrong'}
 if mode=='foreign_source':job['documents'][0]['original']['path']='/another-run/original.pdf'
 write(w/'job.json',job);write(w/'owner-context.json',{'thread_id':os.environ.get('CODEX_THREAD_ID')});shutil.copytree(ROOT,w/'runtime')
 print(json.dumps({'status':'PREPARED_NOT_STARTED','runs':[str(w)]}))
elif cmd=='execute':
 w=Path(a[1]);assert a[2:]==['--detach']
 write(w/'execution-status.json',{'phase':'RUNNING'})
 if mode=='execute_exit':print('synthetic launch failure after possible dispatch',file=sys.stderr);raise SystemExit(9)
 controller={'pid':123456,'pgid':123456,'started':'synthetic identity'}
 if mode=='missing_identity':controller.pop('started')
 print(json.dumps({'status':'DISPATCHED','runs':[str(w)],'controller':controller,'owner_observation':{'registration':'HOST_REGISTRATION_REQUIRED','notifications':'meaningful_changes_only','scheduler':'host_heartbeat','host_tool':'automation_update','host_kind':'heartbeat'}}))
elif cmd in ('observe','cancel'):
 w=Path(a[1])
 if cmd=='cancel':write(w/'cancel-request.json',{'status':'CANCEL_REQUESTED'});print(json.dumps({'status':'CANCEL_REQUESTED'}))
 else:
  done=(w/'case-result.json').exists();paused=(w/'paused.json').exists();alive=(w/'still-live.json').exists()
  row={'run':str(w),'phase':'PAUSED_ERROR' if paused else 'FINISHED' if done else 'RUNNING','terminal_record_present':done and not paused,'process_exit_verified':done and not alive,'paused_errors':[{'incident':'synthetic'}] if paused else [],'live_owned_process_count':1 if alive or not done else 0,'registered_groups_still_present':[123456] if alive else [],'counts':{}}
  if mode=='foreign_observation':row['run']='/another-run/workflow'
  print(json.dumps({'cases':[row],'all_terminal':done and not paused,'all_process_exits_verified':done and not alive,'process_inspection_error':None}))
else:raise SystemExit('No model/proof command allowed in synthetic fixture: '+cmd)
'''


class Fixture(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='yui-benchmark-test-')
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name).resolve()
        self.local = self.base/'relocated checkout with spaces'/'Yui'
        self.local.mkdir(parents=True)
        for name in prepare_yui.STARTUP_FILES:
            shutil.copyfile(BENCHMARK/name, self.local/name)
        self.config = benchmark_config.load_config()
        self.config['formalization']='conditional'
        (self.local/self.config['paper']).write_bytes(b'%PDF synthetic source only')
        self.config['paper_sha256'] = prepare_yui.sha256(self.local/self.config['paper'])
        self.save_config()
        self.install = self.base/'installed skill with spaces'
        for name in REQUIRED:
            path = self.install/name; path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('{}' if path.suffix == '.json' else '')
        (self.install/'SKILL.md').write_text('---\nname: rigorous-proof\ndescription: Synthetic metadata fixture.\n---\n')
        (self.install/'nl0/scripts/basis.py').write_text("def validate_mode(mode,track):\n if mode=='unconditional' and track!='full':raise ValueError('full required')\n")
        (self.install/'nl02lean/scripts/b2lean.py').write_text("import json\ndef validate_receipt(path):\n value=json.loads((path/'report.json').read_text())\n if value.get('status') not in ('WORKFLOW-PASSED','WORKFLOW-CONDITIONAL'):raise ValueError('invalid synthetic closure')\n return value\n")
        (self.install/'nl0/scripts/fault_control.py').write_text("def pending(root):return []\n")
        (self.install/'nl0/scripts/cleanup.py').write_text("from contextlib import nullcontext\ndef cleanup_lock(root):return nullcontext()\ndef inventory(*args,**kwargs):return {'errors':[],'workspaces':{}}\ndef process_table():return {}\ndef discover(*args):return {}\ndef signal_owned(*args):pass\nCORE=None\n")
        (self.install/'auth').mkdir(); (self.install/'auth/auth.json').write_text('{"synthetic":true}')
        (self.install/'config.json').write_text(json.dumps({'timeouts':{'case_seconds':None,'stage_seconds':None,'native_seconds':360},'token_budget':None}))
        scripts = self.install/'nl0/scripts'
        (scripts/'runtime_config.py').write_text(
            "from pathlib import Path\nimport json,os\nfrom datetime import datetime,timezone\nROOT=Path(__file__).resolve().parents[2]\n"
            "def verify():\n if os.environ.get('YUI_TEST_MODE')=='bad_environment':raise ValueError('synthetic toolchain mismatch')\n return {'synthetic_metadata':True,'observed_at_utc':datetime.now(timezone.utc).isoformat()}\n"
            "def auth_home():return ROOT/'auth'\n"
            "def native_timeout():return json.loads((ROOT/'config.json').read_text())['timeouts']['native_seconds']\n")
        (scripts/'entrypoint.py').write_text(
            "def preflight_profiles(job):\n"
            " for phase in ('nl0','lean') if job['track']=='full' else ('nl0',):\n"
            "  if job['profiles'][phase]['id']!='gpt-6.1-sol':raise ValueError('unavailable model')\n"
            "  if job['profiles'][phase]['reasoning_effort']!='high':raise ValueError('unavailable effort')\n")
        (scripts/'target_selection.py').write_text(
            "import hashlib,os,shutil,subprocess\n"
            "def text(path):\n"
            " if os.environ.get('YUI_TEST_MODE')=='empty_pdf':return ''\n"
            " return subprocess.check_output([shutil.which('pdftotext'),'-layout',str(path),'-'],text=True) if shutil.which('pdftotext') else 'Synthetic pypdf fallback text'\n"
            "def select(path,targets,**kwargs):\n"
            " return {'document':{'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest()},'version':'yui-target-selection-1','status':'SELECTED','targets':targets,'full_target':targets[0]['statement'].strip()}\n")
        (scripts/'yui.py').write_text(FAKE_YUI)
        (self.install/'nl02lean/scripts/source_preparation.py').write_text(
            "def read_source(**authority):\n"
            " return ([{'current_standard_receipt_valid':True,'audit_receipt_valid':True,'independent_review_accepted':True,'current_conditional_receipt_valid':False,'source_warnings':[],'unresolved_reviews':[]}],None,None)\n")
        (self.install/'nl02lean/scripts/final_acceptance.py').write_text(
            "import json\ndef validate_receipt(path):\n value=json.loads(path.read_text())\n"
            " if value.get('status') not in ('AUDIT-B-PASSED','AUDIT-B-CONDITIONAL'):raise ValueError('invalid synthetic receipt')\n return value\n")
        self.tools = self.base/'tools with spaces'; self.tools.mkdir()
        self.tool('pdftotext', "import os,sys\nif os.environ.get('YUI_TEST_MODE')=='empty_pdf':raise SystemExit(0)\nprint('Synthetic full paper: definition, theorem, proof, references.')\n")
        self.tool('pdfinfo', "import os\nprint('Pages: broken' if os.environ.get('YUI_TEST_MODE')=='bad_page_count' else 'Pages: 2')\n")
        self.tool('pdftoppm', "from pathlib import Path\nimport os,sys\np=Path(sys.argv[-1])\nfor n in [1] if os.environ.get('YUI_TEST_MODE')=='missing_page' else [1,2]:p.with_name(p.name+'-'+str(n)+'.png').write_bytes(b'synthetic page')\n")
        self.calls = self.base/'runtime calls.jsonl'
        self.registry_calls = self.base/'registry calls.jsonl'
        self.binary = self.base/'fake codex'
        self.entry = {'name':'rigorous-proof','enabled':True,'path':str(self.install/'SKILL.md'),'scope':'user'}
        self.registry = {'data':[{'skills':[self.entry],'errors':[]}]}
        self.write_codex()
        self.env = dict(os.environ, PATH=str(self.tools)+os.pathsep+os.environ.get('PATH',''),
                        YUI_CODEX_BINARY=str(self.binary), YUI_TEST_CALLS=str(self.calls), CODEX_THREAD_ID='fixture-owner')
        self.env.pop('YUI_TEST_MODE', None)

    def save_config(self):
        (self.local/'settings.json').write_text(json.dumps(self.config))

    def tool(self, name, source):
        path = self.tools/name
        path.write_text('#!'+sys.executable+'\n'+source)
        path.chmod(0o700)
        return path

    def write_codex(self, behavior='normal'):
        self.binary.write_text('#!'+sys.executable+'\nimport json,sys,time\n'
            'registry='+repr(self.registry)+'\n'
            'for line in sys.stdin:\n'
            ' value=json.loads(line)\n'
            ' with open('+repr(str(self.registry_calls))+',"a") as out:out.write(json.dumps(value)+"\\n")\n'
            ' if "id" not in value:continue\n'
            ' if value["method"] not in {"initialize","skills/list"}:raise SystemExit(99)\n'
            + (' time.sleep(1)\n' if behavior=='hang' else '')
            + (' raise SystemExit(3)\n' if behavior=='close' else '')
            + (' print(json.dumps({"id":value["id"],"error":{"message":"synthetic registry error"}}),flush=True)\n' if behavior=='error' else
               ' print(json.dumps({"id":value["id"],"result":registry if value["method"]=="skills/list" else {}}),flush=True)\n'))
        self.binary.chmod(0o700)

    def cli(self, *args, ok=True, mode=None):
        env = dict(self.env)
        if mode:env['YUI_TEST_MODE']=mode
        result = subprocess.run([sys.executable,'-B',str(self.local/'prepare_yui.py'),*map(str,args)],
                                cwd=self.base,env=env,capture_output=True,text=True,timeout=25)
        self.assertEqual(result.returncode, 0 if ok else 1, result.stdout+result.stderr)
        value = json.loads(result.stdout)
        return value

    def launch(self, run, **options):
        return self.cli('launch', run, '--heartbeat-id', 'fixture-heartbeat', **options)

    def begin(self, *, run_id=None, mode=None):
        args=['begin']+(['--run-id',run_id] if run_id else [])
        return Path(self.cli(*args,mode=mode)['run'])

    def review(self, run):
        prep=run/'preparation'
        (prep/'checked-source.md').write_text('Synthetic source-only checked full paper.')
        (prep/'target-statement.md').write_text('Synthetic complete Theorem 1 with its definitions and hypotheses.')
        review=json.loads((prep/'source-review.json').read_text())
        review.update(checked_pages=[1,2],transcription_checked=True,target_checked=True,source_only=True)
        (prep/'source-review.json').write_text(json.dumps(review))

    def prepared(self, track='full'):
        self.config['track']=track;self.save_config()
        run=self.begin();self.review(run);self.cli('freeze',run);self.cli('prepare',run)
        return run

    def terminal(self, run, status=None):
        workflow=run/'workflow';job=json.loads((workflow/'job.json').read_text())
        status=status or ('DRAFT-AUDIT-PASSED' if job['track']=='nl0' else 'WORKFLOW-PASSED')
        result={'formalization_goal':job.get('formalization','conditional'),'status':status,'elapsed_case_seconds':1.5,'completion':{'workflow_completed':status!='CANCELLED'},'usage':{'status':'PARTIAL','confirmed_tokens':123}}
        if status!='CANCELLED':
            (workflow/'source-selection.json').write_text(json.dumps({'graph':'synthetic-current-graph'}))
            if job['track']=='full':
                receipt=workflow/'synthetic-machine-acceptance.json'
                receipt.write_text(json.dumps({'status':'AUDIT-B-PASSED','acceptance_basis':'SYNTHETIC_TEST_ONLY','source_conditional':False}))
                result['audit_b']={'receipt_path':str(receipt)}
        if job.get('formalization')=='unconditional' and status in ('WORKFLOW-PASSED','WORKFLOW-CONDITIONAL'):
            closed=workflow/'b2lean';closed.mkdir()
            result['closure']={'unconditional':status=='WORKFLOW-PASSED','kernel_closed':status=='WORKFLOW-PASSED','remaining_premises':[]}
            (closed/'Proof.lean').write_text('SYNTHETIC final proof file; no mathematical certification.')
            (closed/'report.json').write_text(json.dumps({'status':status,'closure':result['closure'],
                'achieved_scope':'UNCONDITIONAL_LEAN' if status=='WORKFLOW-PASSED' else 'CONDITIONAL_LEAN','source_conditional':False}))
        case={'job':{'path':str(workflow/'job.json'),'sha256':prepare_yui.sha256(workflow/'job.json')},'result':result}
        (workflow/'case-result.json').write_text(json.dumps(case))

    def runtime_calls(self):
        return [json.loads(x) for x in self.calls.read_text().splitlines()] if self.calls.exists() else []
