"""Formalization and resource cleanup controls; synthetic metadata only."""
import json
from pathlib import Path
from support import Fixture, benchmark_config, BENCHMARK


class ModeAndCleanupTests(Fixture):
    def unconditional(self):
        self.config.update(track='full',formalization='unconditional');self.save_config()

    def test_checked_in_mode_matches_its_arm(self):
        config=benchmark_config.load_config()
        expected='unconditional' if BENCHMARK.parent.name=='benchmark_uncond' else 'conditional'
        self.assertEqual(config['formalization'],expected)
        self.assertEqual(config['track'],'full' if expected=='unconditional' else 'nl0')

    def test_invalid_modes_and_unconditional_nl0_fail_closed(self):
        for mode in ('',None,'automatic','uncond'):
            self.config['formalization']=mode;self.save_config()
            self.cli('check',ok=False)
        self.config.update(formalization='unconditional',track='nl0');self.save_config()
        self.cli('check',ok=False)
        self.assertEqual(self.runtime_calls(),[])

    def test_unconditional_preparation_keeps_all_original_configuration(self):
        self.unconditional();run=self.prepared()
        job=json.loads((run/'workflow/job.json').read_text())
        self.assertEqual(job['formalization'],'unconditional')
        self.assertEqual(job['profiles'],self.config['profiles'])
        self.assertEqual(job['max_concurrency'], 'auto')
        self.assertNotIn('--max-concurrency', self.runtime_calls()[0])
        self.assertNotIn('--workers', self.runtime_calls()[0])
        self.assertEqual(len(job['documents']),3)
        self.assertIn('--formalization',self.runtime_calls()[0])

    def test_missing_unconditional_support_fails_before_creating_results(self):
        self.unconditional();(self.install/'nl02lean/scripts/b2lean.py').unlink()
        self.cli('begin',ok=False)
        self.assertFalse((self.local/'results').exists());self.assertEqual(self.runtime_calls(),[])

    def test_silent_goal_downgrade_in_prepared_job_is_rejected(self):
        self.unconditional();run=self.begin();self.review(run);self.cli('freeze',run)
        self.cli('prepare',run,mode='wrong_formalization',ok=False)
        self.assertFalse((run/'dispatch-attempt.json').exists())

    def test_unconditional_final_receipt_is_validated(self):
        self.unconditional();run=self.prepared();self.launch(run);self.terminal(run)
        final=self.cli('finish',run)
        self.assertEqual(final['bound_artifact_validation']['basis_closure']['achieved_scope'],'UNCONDITIONAL_LEAN')

    def test_intermediate_only_result_cannot_claim_unconditional_completion(self):
        self.unconditional();run=self.prepared();self.launch(run);self.terminal(run)
        (run/'workflow/b2lean/report.json').unlink()
        self.cli('finish',run,ok=False);self.assertFalse((run/'FINAL_OUTCOME.json').exists())

    def test_qualified_closure_keeps_conditional_status(self):
        self.unconditional();run=self.prepared();self.launch(run);self.terminal(run,'WORKFLOW-CONDITIONAL')
        final=self.cli('finish',run)
        self.assertEqual(final['status'],'WORKFLOW-CONDITIONAL')
        self.assertFalse(final['bound_artifact_validation']['basis_closure']['closure']['unconditional'])

    def test_closure_receipt_drift_prevents_acceptance(self):
        self.unconditional();run=self.prepared();self.launch(run);self.terminal(run)
        p=run/'workflow/b2lean/report.json';data=json.loads(p.read_text());data['closure']['unconditional']=False
        p.write_text(json.dumps(data));self.cli('finish',run,ok=False)

    def test_terminal_cleanup_is_idempotent_and_keeps_evidence(self):
        for mode in ('conditional','unconditional'):
            self.config['formalization']=mode;self.save_config()
            run=self.prepared();self.launch(run);self.terminal(run)
            w=run/'workflow';(w/'Proof.lean').write_text('Synthetic proof source')
            (w/'dead.olean').write_text('disposable');(w/'.DS_Store').write_text('disposable')
            (w/'keep.olean').write_text('evidence');(w/'binding.json').write_text('{"artifact":"keep.olean"}')
            (w/'.pytest_cache').mkdir();(w/'.pytest_cache/cache').write_text('disposable')
            self.assertEqual(self.cli('cleanup',run)['status'],'CLEANED')
            self.assertFalse((w/'dead.olean').exists());self.assertFalse((w/'.DS_Store').exists())
            self.assertFalse((w/'.pytest_cache').exists());self.assertTrue((w/'keep.olean').exists())
            self.assertTrue((w/'Proof.lean').exists());self.assertTrue((w/'runtime').is_dir())
            self.cli('finish',run)
            self.assertEqual(self.cli('cleanup',run)['status'],'CLEANED')

    def test_cleanup_refuses_active_paused_and_modified_job(self):
        run=self.prepared();self.launch(run);self.cli('cleanup',run,ok=False)
        self.terminal(run)
        (run/'workflow/runtime/nl0/scripts/fault_control.py').write_text('def pending(root):return [{}]\n')
        self.cli('cleanup',run,ok=False)
        (run/'workflow/runtime/nl0/scripts/fault_control.py').write_text('def pending(root):return []\n')
        p=run/'workflow/job.json';data=json.loads(p.read_text());data['max_concurrency']=1;p.write_text(json.dumps(data))
        self.terminal(run);self.cli('cleanup',run,ok=False)

    def test_cancelled_run_can_clean_without_claiming_success(self):
        self.unconditional();run=self.prepared();self.launch(run);self.cli('cancel',run)
        self.terminal(run,'CANCELLED')
        self.assertEqual(self.cli('finish',run)['status'],'CANCELLED')
        self.assertEqual(self.cli('cleanup',run)['status'],'CLEANED')
