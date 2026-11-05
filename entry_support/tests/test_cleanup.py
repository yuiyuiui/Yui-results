"""Real neutral ownership/process controls; never starts a model or a proof."""
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest

SUPPORT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(SUPPORT))
from common import digest


def wait_file(path,process,seconds=8):
    until=time.monotonic()+seconds
    while not path.exists() and process.poll() is None and time.monotonic()<until:time.sleep(.02)
    if not path.exists():raise AssertionError('Neutral process did not become ready')


@unittest.skipUnless(os.environ.get('YUI_TEST_INSTALLATION'),'Set YUI_TEST_INSTALLATION for neutral installed-runtime resource tests')
class InstalledResourceCleanup(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='yui-entry-resource-test-');self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name).resolve();self.processes=[];self.scratch=[]
        self.addCleanup(self.reap)
        self.runtime=Path(os.environ['YUI_TEST_INSTALLATION']).resolve()
        self.workflow=self.root/'workflow';source=self.root/'problem.md';source.write_text('Synthetic ownership test only.')
        program="""import json,sys
from pathlib import Path
sys.path.insert(0,str(Path(sys.argv[1])/'nl0/scripts'))
import jobs
from target_selection import select
profiles={phase:{'id':'gpt-6.1-sol','reasoning_effort':'high','speed':'standard','automatic_fallback':False} for phase in ('nl0','lean')}
target=select(Path(sys.argv[2]),[{'id':'neutral','label':'Neutral source','statement':'Synthetic ownership test only.','start_line':1}])
print(json.dumps(jobs.prepare(Path(sys.argv[2]),track='full',profiles=profiles,output=Path(sys.argv[3]),formalization='unconditional',target=target)))
"""
        result=subprocess.run([sys.executable,'-B','-c',program,str(self.runtime),str(source),str(self.workflow)],capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stderr)
        self.frozen=self.workflow/'runtime';self.terminal()

    def terminal(self):
        (self.workflow/'case-result.json').write_text(json.dumps({'job':{'path':str(self.workflow/'job.json'),'sha256':digest(self.workflow/'job.json')},
            'result':{'status':'CANCELLED','formalization_goal':'unconditional'}}))

    def reap(self):
        for p in self.processes:
            if p.poll() is None:p.kill()
            p.wait(timeout=5)
        for row in self.scratch:
            try:os.kill(row['child'],signal.SIGKILL)
            except ProcessLookupError:pass
            shutil.rmtree(row['work'],ignore_errors=True)

    def owner(self,stubborn=False):
        ready=self.workflow/'ready.json'
        code="""import json,os,signal,subprocess,sys,tempfile,time
from pathlib import Path
sys.path.insert(0,str(Path(sys.argv[1])/'nl0/scripts'))
from run_resources import register_workspace,register_child
from execution_state import identity
logs=Path(sys.argv[2]);work=Path(tempfile.mkdtemp(prefix='yui-entry-neutral-work-'))
register_workspace(work,logs)
child=subprocess.Popen([sys.executable,'-B','-c','import time;time.sleep(60)'])
register_child(work,child,'neutral-child')
if sys.argv[3]=='yes':signal.signal(signal.SIGTERM,signal.SIG_IGN)
(logs/'case-process.json').write_text(json.dumps({'schema_version':'yui-owned-process-1','process':identity(os.getpid())}))
(logs/'ready.json').write_text(json.dumps({'work':str(work),'child':child.pid}))
time.sleep(60)
"""
        p=subprocess.Popen([sys.executable,'-B','-c',code,str(self.frozen),str(self.workflow),'yes' if stubborn else 'no'],start_new_session=True)
        self.processes.append(p);wait_file(ready,p);row=json.loads(ready.read_text());self.scratch.append(row);return p,row

    def clean(self,ok=True,*,cleaner=SUPPORT/'resource_cleanup.py'):
        result=subprocess.run([sys.executable,'-B',str(cleaner),str(self.workflow),str(self.frozen)],capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0 if ok else 1,result.stdout+result.stderr)
        return json.loads(result.stdout)

    def retain(self,path):
        record=self.workflow/'result.json'
        record.write_text(json.dumps({'workspace_retention':{'workspace':str(path)}}))
        return record

    def test_reaps_owned_processes_and_scratch_preserving_sources_shared_links_and_evidence(self):
        owner,row=self.owner(stubborn=True)
        unrelated=subprocess.Popen([sys.executable,'-B','-c','import time;time.sleep(60)'],start_new_session=True);self.processes.append(unrelated)
        external=self.root/'external';external.mkdir();(external/'keep.olean').write_text('shared cache')
        (self.workflow/'linked-packages').symlink_to(external,target_is_directory=True)
        for filename in ('Proof.lean','keep.olean','unused.olean','.DS_Store'):(self.workflow/filename).write_text(filename)
        (self.workflow/'evidence.json').write_text('{"artifact":"keep.olean"}')
        cache=self.workflow/'.pytest_cache';cache.mkdir();(cache/'unused.pyc').write_text('cache')
        self.assertEqual(self.clean()['status'],'CLEANED');owner.wait(timeout=5)
        self.assertFalse(Path(row['work']).exists());self.assertIsNone(unrelated.poll())
        for filename in ('unused.olean','.DS_Store','.pytest_cache'):self.assertFalse((self.workflow/filename).exists())
        for filename in ('Proof.lean','keep.olean','case-result.json','job.json'):self.assertTrue((self.workflow/filename).is_file())
        self.assertTrue((external/'keep.olean').is_file());self.assertTrue((self.frozen/'SKILL.md').is_file())
        self.assertEqual(self.clean()['status'],'CLEANED')

    def test_active_or_paused_state_keeps_processes_and_scratch(self):
        owner,row=self.owner();(self.workflow/'case-result.json').unlink()
        self.assertEqual(self.clean(False)['status'],'CLEANUP_BLOCKED');self.assertIsNone(owner.poll())
        self.terminal();(self.workflow/'error-state.json').write_text('{"state":"PAUSED_ERROR"}')
        self.clean(False);self.assertIsNone(owner.poll());self.assertTrue(Path(row['work']).exists())

    def test_wrong_owner_marker_blocks_deletion_and_signal(self):
        owner,row=self.owner();(Path(row['work'])/'.yui-workspace-owner.json').write_text('{}')
        self.clean(False);self.assertIsNone(owner.poll());self.assertTrue(Path(row['work']).exists())

    def test_retained_workspace_health_evidence_is_not_invalidated(self):
        owner,row=self.owner()
        self.retain(row['work'])
        self.clean(False);self.assertIsNone(owner.poll());self.assertTrue(Path(row['work']).exists())

    def test_retained_parent_alias_blocks_all_entry_cleaners_before_signalling(self):
        owner,row=self.owner()
        work=Path(row['work']).resolve()
        alias=self.root/'temporary-directory-alias'
        alias.symlink_to(work.parent,target_is_directory=True)
        recorded=alias/work.name
        self.assertNotEqual(str(work),str(recorded))
        self.assertTrue(work.samefile(recorded))
        record=self.retain(recorded);before=record.read_bytes()
        evidence=work/'retained-evidence.txt';evidence.write_text('neutral stage evidence')
        for entry in (SUPPORT,SUPPORT.parent/'benchmark_cond/Yui',SUPPORT.parent/'benchmark_uncond/Yui'):
            result=self.clean(False,cleaner=entry/'resource_cleanup.py')
            self.assertEqual(result['status'],'CLEANUP_BLOCKED',entry)
            self.assertIn('Runtime must release',result['error'])
            self.assertIsNone(owner.poll())
            os.kill(row['child'],0)
            self.assertEqual(evidence.read_text(),'neutral stage evidence')
            self.assertEqual(record.read_bytes(),before)

    def test_unresolvable_retained_link_blocks_until_it_identifies_a_distinct_workspace(self):
        owner,row=self.owner();work=Path(row['work'])
        alias=self.root/'retained-work'
        alias.symlink_to(alias,target_is_directory=True)
        record=self.retain(alias);before=record.read_bytes()
        self.assertEqual(self.clean(False)['status'],'CLEANUP_BLOCKED')
        self.assertIsNone(owner.poll());os.kill(row['child'],0)
        self.assertTrue(work.is_dir())
        other=self.root/'separate'/work.name;other.mkdir(parents=True)
        evidence=other/'keep.txt';evidence.write_text('another directory')
        alias.unlink();alias.symlink_to(other,target_is_directory=True)
        self.assertFalse(work.samefile(alias))
        self.assertEqual(self.clean()['status'],'CLEANED')
        self.assertFalse(work.exists());self.assertIsNotNone(owner.poll())
        self.assertEqual(evidence.read_text(),'another directory')
        self.assertEqual(record.read_bytes(),before)

    def test_missing_retained_path_requires_verified_release_before_cleaning_other_scratch(self):
        owner,row=self.owner();work=Path(row['work'])
        released=self.root/'released-work';released.mkdir();released.rmdir()
        retention={'workspace':str(released),'logs':str(self.workflow),'status':'OWNED_RETAINED'}
        record=self.workflow/'result.json'
        record.write_text(json.dumps({'workspace_retention':retention,'temporary_workspace_removed':False}))
        before=record.read_bytes()
        receipt={'workspace_retention':retention,'cleanup_confirmed':True,'authorization':'ROLE_COMPLETED',
                 'result_sha256':digest(record)}
        release=self.workflow/'resources/release.json'
        for invalid in (None,{**receipt,'result_sha256':'0'*64}):
            if invalid:release.write_text(json.dumps(invalid))
            self.assertEqual(self.clean(False)['status'],'CLEANUP_BLOCKED')
            self.assertIsNone(owner.poll());self.assertTrue(work.is_dir())
        release.write_text(json.dumps(receipt))
        self.assertEqual(self.clean()['status'],'CLEANED')
        self.assertFalse(work.exists());self.assertIsNotNone(owner.poll())
        self.assertEqual(record.read_bytes(),before)

    def test_ambiguous_retention_blocks_and_explicit_legacy_removal_allows_cleanup(self):
        owner,row=self.owner();work=Path(row['work']);record=self.workflow/'result.json'
        for invalid in ('malformed',{'status':'OWNED_RETAINED'},{'workspace':23},{'workspace':'relative'}):
            with self.subTest(retention=invalid):
                record.write_text(json.dumps({'workspace_retention':invalid}))
                self.assertEqual(self.clean(False)['status'],'CLEANUP_BLOCKED')
                self.assertIsNone(owner.poll());self.assertTrue(work.is_dir())
        record.write_text(json.dumps({'workspace_retention':{'workspace':str(self.root/'old-work')},
                                      'temporary_workspace_removed':True}))
        self.assertEqual(self.clean()['status'],'CLEANED')
        self.assertFalse(work.exists());self.assertIsNotNone(owner.poll())

    def test_job_binding_and_symlink_boundaries_are_enforced(self):
        p=self.workflow/'case-result.json';record=json.loads(p.read_text());record['job']['sha256']='0'*64;p.write_text(json.dumps(record))
        self.clean(False);self.terminal()
        alias=self.root/'alias';alias.symlink_to(self.workflow,target_is_directory=True)
        result=subprocess.run([sys.executable,'-B',str(SUPPORT/'resource_cleanup.py'),str(alias),str(self.frozen)],capture_output=True,text=True,timeout=20)
        self.assertEqual(result.returncode,1);self.assertTrue(self.workflow.exists())


class TestRunnerCleanup(unittest.TestCase):
    def test_success_failure_and_sigterm_all_reclaim_background_processes_and_hidden_scratch(self):
        import run_checks
        with tempfile.TemporaryDirectory(prefix='entry-runner-control-') as temp:
            for mode in ('success','failure','interrupt'):
                with self.subTest(mode=mode):
                    receipt=Path(temp)/mode
                    task="""import json,os,subprocess,sys,time
from pathlib import Path
root=Path(os.environ['YUI_ENTRY_CHECK_ROOT']);(root/'.hidden-junk').write_text('temporary')
child=subprocess.Popen([sys.executable,'-B','-c','import time;time.sleep(60)'])
Path(sys.argv[1]).write_text(json.dumps({'root':str(root),'child':child.pid}))
time.sleep(60) if sys.argv[2]=='interrupt' else time.sleep(.4)
raise SystemExit(7 if sys.argv[2]=='failure' else 0)
"""
                    outer="import sys;sys.path.insert(0,sys.argv[1]);import run_checks;raise SystemExit(run_checks.run(command=[sys.executable,'-B','-c',sys.argv[2],sys.argv[3],sys.argv[4]]))"
                    p=subprocess.Popen([sys.executable,'-B','-c',outer,str(SUPPORT),task,str(receipt),mode],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True)
                    try:
                        wait_file(receipt,p);record=json.loads(receipt.read_text())
                        if mode=='interrupt':p.send_signal(signal.SIGTERM)
                        stdout,stderr=p.communicate(timeout=15)
                        self.assertEqual(p.returncode,{'success':0,'failure':7,'interrupt':143}[mode],stdout+stderr)
                        self.assertIn('test cleanup: CLEANED',stdout)
                        self.assertFalse(Path(record['root']).exists())
                        row=run_checks.process_table().get(record['child'])
                        self.assertTrue(row is None or row['stat'].startswith('Z'))
                    finally:
                        if p.poll() is None:p.kill();p.wait(timeout=5)


if __name__=='__main__':unittest.main()
