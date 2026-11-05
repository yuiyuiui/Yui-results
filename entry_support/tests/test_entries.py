"""Entry wiring controls; fake registry/runtime never performs mathematics."""
from pathlib import Path
import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

REPO=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(REPO/'benchmark_cond/Yui/tests'))
from support import Fixture
sys.path.insert(0,str(REPO/'entry_support'))
from exercise_entry import Entry,target_section
import exercise_entry
from common import digest,terminal_ready


class ExerciseEntries(Fixture):
    def setUp(self):
        super().setUp()
        self.entry_root=self.base/'relocated checkout with spaces/test_uncond/geometry-product-dimension'
        self.entry_root.mkdir(parents=True)
        source=REPO/'test_uncond/geometry-product-dimension'
        for name in ('README.md','settings.json','run_test.py'):shutil.copyfile(source/name,self.entry_root/name)
        self.problem='# Synthetic input\n\n## Fixed interpretation and complete target\n\nFor n a natural number, prove n=n.\n\n## Fixed natural-language proof\n\nReflexivity.\n'
        (self.entry_root/'problem.md').write_text(self.problem)
        c=json.loads((self.entry_root/'settings.json').read_text());c['input_sha256']=digest(self.entry_root/'problem.md')
        (self.entry_root/'settings.json').write_text(json.dumps(c))
        self.entry=Entry(self.entry_root)
        self.environment=patch.dict(os.environ,self.env);self.environment.start();self.addCleanup(self.environment.stop)

    def mode(self,value):
        p=self.entry_root/'settings.json';c=json.loads(p.read_text());c['formalization']=value;p.write_text(json.dumps(c))

    def source_review(self,run):
        p=run/'preparation/source-review.json';r=json.loads(p.read_text())
        r.update(source_read=True,target_checked=True,source_only=True,notes='SYNTHETIC source readback control.')
        p.write_text(json.dumps(r))

    def started(self,mode='unconditional'):
        self.mode(mode);run=Path(self.entry.begin()['run']);self.source_review(run);self.entry.prepare(run);return run

    def test_checked_in_six_entries_have_pinned_source_and_exact_goals(self):
        for family,mode in [('test_cond','conditional'),('test_uncond','unconditional')]:
            for root in sorted((REPO/family).iterdir()):
                with self.subTest(root=root):
                    c=Entry(root).config();self.assertEqual(c['formalization'],mode);self.assertEqual(c['track'],'full')
                    self.assertEqual(c['input_sha256'],digest(root/'problem.md'))
                    source=(root/'problem.md').read_text();body,_,_=target_section(source,c['target_heading'])
                    self.assertTrue(body);self.assertNotIn('## Fixed natural-language proof',body)
                    readme=(root/'README.md').read_text()
                    for command in ('begin','prepare','launch','observe','finish','cleanup'):
                        self.assertIn('run_test.py '+command,readme)
                    self.assertIn('CLEANUP.json',readme)

    def test_unconditional_begin_freezes_only_current_source_without_dispatch(self):
        run=Path(self.entry.begin()['run']);r=json.loads((run/'TEST_RUN.json').read_text())
        self.assertEqual(r['status'],'SOURCE_REVIEW_REQUIRED');self.assertEqual(self.runtime_calls(),[])
        self.assertEqual((run/'preparation/problem.md').read_text(),self.problem)
        self.assertTrue((run/'preparation/startup/entry_support/resource_cleanup.py').is_file())
        self.assertFalse((run/'workflow').exists())

    def test_missing_unconditional_runtime_blocks_before_run_creation(self):
        (self.install/'nl0/scripts/basis.py').unlink()
        with self.assertRaisesRegex(ValueError,'lacks unconditional'):self.entry.begin()
        self.assertFalse((self.entry_root/'rigorous-proof').exists());self.assertEqual(self.runtime_calls(),[])

    def test_runtime_budget_drift_blocks_before_run_creation(self):
        p=self.install/'config.json';c=json.loads(p.read_text());c['timeouts']['stage_seconds']=60;p.write_text(json.dumps(c))
        with self.assertRaisesRegex(ValueError,'runtime limits'):self.entry.begin()
        self.assertFalse((self.entry_root/'rigorous-proof').exists());self.assertEqual(self.runtime_calls(),[])

    def test_conditional_works_with_legacy_runtime_and_no_mode_flag(self):
        self.mode('conditional');(self.install/'nl0/scripts/basis.py').unlink()
        run=Path(self.entry.begin()['run']);self.source_review(run);self.entry.prepare(run)
        job=json.loads((run/'workflow/job.json').read_text());self.assertEqual(job['formalization'],'conditional')
        self.assertNotIn('--formalization',self.runtime_calls()[0])

    def test_both_modes_forward_profiles_workers_fresh_target_and_only_two_documents(self):
        for mode in ('conditional','unconditional'):
            with self.subTest(mode=mode):
                run=self.started(mode);job=json.loads((run/'workflow/job.json').read_text())
                self.assertEqual(job['formalization'],mode);self.assertEqual(job['max_concurrency'],10)
                self.assertEqual([d['id'] for d in job['documents']],['problem.md','target-selection.json'])
                self.assertEqual(job['target_selection']['document']['path'],str(run/'preparation/problem.md'))
                self.assertIn('For n a natural number',job['target_selection']['full_target'])

    def test_source_readback_false_extra_or_changed_target_prevents_prepare(self):
        run=Path(self.entry.begin()['run'])
        with self.assertRaisesRegex(ValueError,'readback'):self.entry.prepare(run)
        self.source_review(run);p=run/'preparation/target-statement.md';p.write_text('True')
        with self.assertRaisesRegex(ValueError,'changed'):self.entry.prepare(run)
        self.assertEqual(self.runtime_calls(),[])

    def test_changed_source_profile_goal_or_entry_blocks_start(self):
        for filename in ('problem.md','README.md','settings.json'):
            run=Path(self.entry.begin()['run']);self.source_review(run);p=self.entry_root/filename;raw=p.read_bytes()
            try:
                if filename=='settings.json':c=json.loads(raw);c['formalization']='conditional';p.write_text(json.dumps(c))
                else:p.write_bytes(raw+b'\nchanged')
                with self.subTest(filename=filename),self.assertRaises(ValueError):self.entry.prepare(run)
            finally:p.write_bytes(raw)

    def test_unregistered_or_wrong_chat_cannot_dispatch(self):
        run = self.started()
        with self.assertRaisesRegex(ValueError, '--heartbeat-id'):
            self.entry.launch(run)
        with patch.dict(os.environ, {'CODEX_THREAD_ID':'foreign-owner'}), self.assertRaisesRegex(ValueError, 'different owner'):
            self.entry.launch(run, heartbeat_id='fixture-heartbeat')
        self.assertEqual([call[0] for call in self.runtime_calls()], ['prepare'])
        self.assertFalse((run/'dispatch-attempt.json').exists())
        self.assertFalse((run/'OWNER_MONITOR_STATE.json').exists())

    def test_duplicate_begin_prepare_and_launch_preserve_first_attempt(self):
        run=Path(self.entry.begin('fixed')['run']);self.source_review(run);self.entry.prepare(run)
        with self.assertRaises(FileExistsError):self.entry.begin('fixed')
        with self.assertRaises(ValueError):self.entry.prepare(run)
        handoff = self.entry.launch(run, heartbeat_id='fixture-heartbeat')['owner_observation']
        state = json.loads((run/'OWNER_MONITOR_STATE.json').read_text())
        self.assertEqual(state['automation_id'], 'fixture-heartbeat')
        self.assertEqual(state['target_thread_id'], 'fixture-owner')
        self.assertEqual(state['runs'], [str(run/'workflow')])
        self.assertEqual(state['observe_command'][-3:], [str(self.entry_root/'run_test.py'), 'observe', str(run)])
        self.assertEqual(handoff['notifications'], 'every_wake')
        self.assertEqual(handoff['foreground'], 'end_turn_after_handoff')
        with self.assertRaises(ValueError):self.entry.launch(run, heartbeat_id='fixture-heartbeat')
        self.assertEqual([r[0] for r in self.runtime_calls()],['prepare','execute'])

    def test_interrupted_before_dispatch_reuses_only_the_same_heartbeat(self):
        run = self.started()
        write = exercise_entry.write
        def interrupted(path, value, **options):
            if path.name == 'dispatch-attempt.json':
                raise OSError('Synthetic interruption before dispatch')
            return write(path, value, **options)
        with patch.object(exercise_entry, 'write', side_effect=interrupted), self.assertRaises(OSError):
            self.entry.launch(run, heartbeat_id='original')
        with self.assertRaisesRegex(ValueError, 'different heartbeat'):
            self.entry.launch(run, heartbeat_id='other')
        self.assertFalse((run/'dispatch-attempt.json').exists())
        self.entry.launch(run, heartbeat_id='original')
        self.assertEqual([args[0] for args in self.runtime_calls()], ['prepare','execute'])

    def test_foreign_run_symlink_and_changed_prepared_input_rejected(self):
        run=self.started();alias=run.parent/'alias';alias.symlink_to(run,target_is_directory=True)
        with self.assertRaises(ValueError):self.entry.owned(alias)
        (run/'workflow/inputs/problem.md').write_text('different')
        with self.assertRaises(ValueError):self.entry.launch(run, heartbeat_id='fixture-heartbeat')

    def test_actual_final_unconditional_scope_is_required_and_reported(self):
        run=self.started();self.entry.launch(run, heartbeat_id='fixture-heartbeat');self.terminal(run)
        final=self.entry.finish(run)
        self.assertEqual(final['validation']['basis_closure']['achieved_scope'],'UNCONDITIONAL_LEAN')
        self.assertTrue((run/'FINAL_REPORT.zh.md').exists())
        with self.assertRaises(ValueError):self.entry.finish(run)

    def test_conditional_intermediate_cannot_close_unconditional_goal(self):
        run=self.started();self.entry.launch(run, heartbeat_id='fixture-heartbeat');self.terminal(run)
        (run/'workflow/b2lean/report.json').unlink()
        with self.assertRaises(ValueError):self.entry.finish(run)
        self.assertFalse((run/'FINAL_OUTCOME.json').exists())

    def test_draft_only_acceptance_cannot_close_unconditional_full_goal(self):
        run=self.started();self.entry.launch(run, heartbeat_id='fixture-heartbeat');self.terminal(run,'DRAFT-AUDIT-PASSED')
        with self.assertRaises(ValueError):self.entry.finish(run)

    def test_malformed_configuration_never_dispatches(self):
        p=self.entry_root/'settings.json';valid=p.read_text()
        changes=[{'track':'nl0'},{'workers':True},{'workers':0},{'input':'../problem.md'},
                 {'limits':{}},{'profiles':{}},{'case_id':'foreign'},{'formalization':'automatic'}]
        for change in changes:
            c=json.loads(valid);c.update(change);p.write_text(json.dumps(c))
            with self.subTest(change=change),self.assertRaises((ValueError,TypeError)):self.entry.begin()
        p.write_text(valid);self.assertEqual(self.runtime_calls(),[])

    def test_unconditional_goal_drift_and_foreign_receipt_fail(self):
        for changed in ('goal','receipt'):
            run=self.started();self.entry.launch(run, heartbeat_id='fixture-heartbeat');self.terminal(run)
            p=run/'workflow/case-result.json';c=json.loads(p.read_text())
            if changed=='goal':c['result']['formalization_goal']='conditional'
            else:c['result']['audit_b']['receipt_path']=str(self.base/'foreign.json')
            p.write_text(json.dumps(c))
            with self.subTest(changed=changed),self.assertRaises(ValueError):self.entry.finish(run)

    def test_paused_and_unverified_exit_cannot_finish(self):
        run=self.started();self.entry.launch(run, heartbeat_id='fixture-heartbeat');self.terminal(run)
        for filename in ('paused.json','still-live.json'):
            p=run/'workflow'/filename;p.write_text('{}')
            with self.subTest(filename=filename),self.assertRaises(ValueError):self.entry.finish(run)
            p.unlink()

    def test_cleanup_preserves_bound_compilation_evidence_and_proof(self):
        run=self.started();self.entry.launch(run, heartbeat_id='fixture-heartbeat');self.terminal(run);self.entry.finish(run)
        w=run/'workflow';(w/'dead.olean').write_text('unneeded');(w/'keep.olean').write_text('bound evidence')
        (w/'reference.json').write_text('{"path":"keep.olean","sha256":"synthetic"}')
        (w/'__pycache__').mkdir();(w/'__pycache__/dead.pyc').write_text('cache')
        before=(w/'b2lean/Proof.lean').read_bytes()
        result=self.entry.cleanup(run)
        self.assertEqual(result['status'],'CLEANED');self.assertFalse((w/'dead.olean').exists())
        self.assertTrue((w/'keep.olean').exists());self.assertFalse((w/'__pycache__').exists())
        self.assertEqual((w/'b2lean/Proof.lean').read_bytes(),before)
        self.assertEqual(self.entry.cleanup(run)['status'],'CLEANED')

    def test_cleanup_refuses_no_terminal_result_and_foreign_path(self):
        run=self.started()
        with self.assertRaises(ValueError):self.entry.cleanup(run)
        with self.assertRaises(ValueError):self.entry.cleanup(self.base)

    def test_target_section_rejects_missing_duplicate_and_wrong_section(self):
        heading='## Fixed interpretation and complete target'
        for source in ('# no target',heading+'\n'+heading+'\nTrue'):
            with self.assertRaises(ValueError):target_section(source,heading)
        p=self.entry_root/'settings.json';c=json.loads(p.read_text());c['target_heading']='## Fixed natural-language proof';p.write_text(json.dumps(c))
        with self.assertRaises(ValueError):self.entry.config()


class SnapshotTests(unittest.TestCase):
    def test_terminal_predicate_is_strict(self):
        self.assertFalse(terminal_ready(None));self.assertFalse(terminal_ready({'cases':[]}))
        base={'all_terminal':True,'all_process_exits_verified':True,'process_inspection_error':None,
            'cases':[{'terminal_record_present':True,'process_exit_verified':True,'phase':'FINISHED',
                'counts':{},'paused_errors':[],'live_owned_process_count':0,'registered_groups_still_present':[]}]}
        self.assertTrue(terminal_ready(base))
        for key,value in [('phase','PAUSED_ERROR'),('paused_errors',[1]),('live_owned_process_count',False),('registered_groups_still_present',[2])]:
            row=copy.deepcopy(base);row['cases'][0][key]=value
            self.assertFalse(terminal_ready(row))


@unittest.skipUnless(os.environ.get('YUI_TEST_INSTALLATION'),'Set YUI_TEST_INSTALLATION for real prepare compatibility; no dispatch')
class InstalledExercisePreparation(unittest.TestCase):
    def test_real_prepare_preserves_both_goals_and_complete_source(self):
        runtime=Path(os.environ['YUI_TEST_INSTALLATION']).resolve()
        registered={'root':str(runtime),'skill_md':str(runtime/'SKILL.md'),'skill_sha256':digest(runtime/'SKILL.md')}
        with tempfile.TemporaryDirectory(prefix='entry-prepare-contract-') as directory:
            for mode,family in [('conditional','test_cond'),('unconditional','test_uncond')]:
                with self.subTest(mode=mode):
                    root=Path(directory)/family/'geometry-product-dimension';root.mkdir(parents=True)
                    for name in ('README.md','settings.json','run_test.py'):shutil.copyfile(REPO/family/root.name/name,root/name)
                    (root/'problem.md').write_text('# Neutral source\n\n## Fixed interpretation and complete target\n\nFor every n : Nat, n = n.\n\n## Fixed natural-language proof\n\nReflexivity.\n')
                    config=json.loads((root/'settings.json').read_text());config['input_sha256']=digest(root/'problem.md')
                    (root/'settings.json').write_text(json.dumps(config));entry=Entry(root)
                    with patch('exercise_entry.require_skill',return_value=registered):
                        run=Path(entry.begin()['run']);p=run/'preparation/source-review.json';review=json.loads(p.read_text())
                        review.update(source_read=True,target_checked=True,source_only=True,notes='Neutral source readback for prepare API validation only.')
                        p.write_text(json.dumps(review));entry.prepare(run)
                    record=json.loads((run/'TEST_RUN.json').read_text());job=entry.validate_job(run,record)
                    self.assertEqual(job['formalization'],mode)
                    self.assertIn('For every n : Nat',job['target_selection']['full_target'])
                    self.assertEqual(len(job['documents']),2)
                    self.assertFalse((run/'dispatch-attempt.json').exists())
                    self.assertFalse((run/'workflow/execution-status.json').exists())


if __name__=='__main__':unittest.main()
