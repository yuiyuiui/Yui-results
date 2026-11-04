"""Passive one-turn native CLI recorder. Explicit owner invokes each continuation."""
import datetime,json,os,pathlib,subprocess,sys,time,hashlib,shutil
root=pathlib.Path(__file__).resolve().parent.parent
owner=root/'owner-records'
runtime=json.loads((owner/'runtime.json').read_text())
turn=int(sys.argv[1]); session=sys.argv[2] if len(sys.argv)>2 else None
stem=f'author-{turn:03d}'
prompt=owner/f'author-prompt-{turn:03d}.md'
assert prompt.exists()
env=os.environ.copy()
removed=[]
for key in list(env):
 if key.startswith(('CODEX_','OPENAI_','CHATGPT_')):
  removed.append(key);env.pop(key)
env['CODEX_HOME']=runtime['codex_home'];env['LEAN_PATH']=runtime['lean_path']
env.update(runtime.get('transport_environment',{}))
args=[shutil.which('codex'),'--no-daemon','exec','--strict-config','--skip-git-repo-check','--json','-m','gpt-6.1-sol','-c','model_reasoning_effort="high"','-c','service_tier="default"','-o',str(owner/f'{stem}-last-message.md')]
if session:
 args=[shutil.which('codex'),'--no-daemon','exec','resume','--strict-config','--skip-git-repo-check','--json','-m','gpt-6.1-sol','-c','model_reasoning_effort="high"','-c','service_tier="default"','-o',str(owner/f'{stem}-last-message.md'),session,'-']
else:args+=['-']
start=time.time(); mono=time.monotonic()
record={'turn':turn,'session_to_resume':session,'argv':args,'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'start_epoch':start,'prompt_sha256':hashlib.sha256(prompt.read_bytes()).hexdigest(),'recorder_pid':os.getpid(),'pgid':os.getpgrp(),'removed_environment_names':removed,'requested_profile':runtime['requested_profile'],'actual_provider_routing':'UNVERIFIED','transport_environment':runtime.get('transport_environment',{})}
with prompt.open('rb') as inp,(owner/f'{stem}.jsonl').open('wb') as out,(owner/f'{stem}.stderr').open('wb') as err:
 child=subprocess.Popen(args,cwd=runtime['work'],env=env,stdin=inp,stdout=out,stderr=err)
 record['native_pid']=child.pid
 record['native_identity']=subprocess.check_output(['ps','-p',str(child.pid),'-o','pid=,ppid=,pgid=,lstart=,command='],text=True).strip()
 (owner/f'{stem}-process.json').write_text(json.dumps(record,indent=2))
 code=child.wait()
record.update(exit_code=code,end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-mono)
(owner/f'{stem}-exit.json').write_text(json.dumps(record,indent=2))
