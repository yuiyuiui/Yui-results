"""End-to-end stage boundaries against real local fake executables, not models."""
from pathlib import Path
import json
import subprocess
from unittest.mock import patch
import unittest

from support import Fixture, prepare_yui


class PipelineTests(Fixture):
    def record(self, run):return json.loads((run/'BENCHMARK_RUN.json').read_text())

    def test_begin_creates_only_own_source_and_review_records(self):
        run=self.begin()
        self.assertEqual(self.record(run)['status'],'SOURCE_REVIEW_REQUIRED')
        self.assertFalse(self.record(run)['model_started'])
        prep=run/'preparation'
        self.assertEqual((prep/'original.pdf').read_bytes(),(self.local/self.config['paper']).read_bytes())
        self.assertEqual(len(list((prep/'pages').glob('*.png'))),2)
        self.assertEqual((prep/'checked-source.md').read_bytes(),(prep/'extracted.md').read_bytes())
        self.assertFalse(json.loads((prep/'source-review.json').read_text())['target_checked'])
        self.assertFalse((run/'workflow').exists())
        self.assertFalse((self.local/'.prepared').exists())
        self.assertEqual(self.runtime_calls(),[])

    def test_pypdf_fallback_is_available_without_pdftotext_or_sibling_files(self):
        (self.tools/'pdftotext').unlink()
        (self.install/'nl0/scripts/pypdf.py').write_text('# Synthetic import availability only.\n')
        self.tool('git','raise SystemExit(1)\n')
        self.env['PATH']=str(self.tools)
        value=self.cli('check')
        self.assertEqual(value['environment']['pdf_text_method'],'pypdf-text')
        run=self.begin()
        self.assertEqual((run/'preparation/extracted.md').read_text(),'Synthetic pypdf fallback text')
        self.assertEqual(self.record(run)['status'],'SOURCE_REVIEW_REQUIRED')
        self.assertEqual(self.runtime_calls(),[])

    def test_missing_pdf_renderer_is_an_actionable_preflight_failure(self):
        (self.tools/'pdftoppm').unlink()
        self.env['PATH']=str(self.tools)
        self.tool('git','raise SystemExit(1)\n')
        value=self.cli('check',ok=False)
        self.assertIn('pdftoppm',value['error'])
        self.assertFalse((self.local/'results').exists())
        self.assertEqual(self.runtime_calls(),[])

    def test_existing_run_and_invalid_run_ids_do_not_overwrite(self):
        run=self.begin(run_id='fixed-id');before=(run/'BENCHMARK_RUN.json').read_bytes()
        self.cli('begin','--run-id','fixed-id',ok=False)
        self.assertEqual((run/'BENCHMARK_RUN.json').read_bytes(),before)
        for name in ['../old','/outside','.','..','bad/id']:
            with self.subTest(name=name):self.cli('begin','--run-id',name,ok=False)
        self.assertEqual(self.runtime_calls(),[])

    def test_results_symlink_and_foreign_run_are_rejected(self):
        (self.local/'results').symlink_to(self.base,target_is_directory=True)
        self.assertIn('symlinks',self.cli('begin',ok=False)['error'])
        (self.local/'results').unlink()
        outside=self.base/'old-run';outside.mkdir()
        self.assertIn('owned results',self.cli('freeze',outside,ok=False)['error'])
        self.assertEqual(self.runtime_calls(),[])

    def test_partial_write_failure_keeps_the_failed_preparation_record(self):
        checked=self.cli('check')
        def local_path(value,*,root=self.local):
            from support import benchmark_config
            return benchmark_config.local_path(value,root=root)
        with patch.object(prepare_yui,'ROOT',self.local),patch.object(prepare_yui,'local_path',side_effect=local_path),patch.object(prepare_yui,'checked_environment',return_value=(self.config,checked['installed'],checked['bindings'],checked['environment'])),patch.object(prepare_yui.shutil,'copyfile',side_effect=OSError('synthetic write failure')):
            with self.assertRaises(prepare_yui.RunFailure) as caught:prepare_yui.begin(run_id='write-failure')
        run=Path(caught.exception.run)
        self.assertEqual(self.record(run)['status'],'PREPARATION_FAILED')
        self.assertIn('synthetic write failure',self.record(run)['failure']['detail'])
        self.assertFalse((run/'workflow').exists())
        self.assertEqual(self.runtime_calls(),[])

    def test_cancel_during_source_preparation_cannot_later_dispatch(self):
        run=self.begin()
        value=self.cli('cancel',run)
        self.assertEqual(value['status'],'CANCELLED_PREPARATION')
        self.assertFalse(value['yui_model_dispatched'])
        self.cli('freeze',run,ok=False);self.launch(run,ok=False)
        self.assertTrue((run/'preparation/original.pdf').is_file())
        self.assertEqual(self.runtime_calls(),[])

    def test_source_extraction_and_rendering_errors_retain_failed_run(self):
        for mode in ['empty_pdf','bad_page_count','missing_page']:
            with self.subTest(mode=mode):
                value=self.cli('begin','--run-id',mode,ok=False,mode=mode)
                run=Path(value['run'])
                self.assertTrue(run.is_dir())
                record=self.record(run)
                self.assertEqual(record['status'],'PREPARATION_FAILED')
                self.assertFalse(record['model_started'])
                self.assertFalse(record['failure']['automatic_retry'])
                self.assertFalse((run/'workflow').exists())
        self.assertEqual(self.runtime_calls(),[])

    def test_unreviewed_source_cannot_prepare_or_freeze(self):
        run=self.begin()
        self.assertIn('only after',self.cli('prepare',run,ok=False)['error'])
        self.assertIn('every PDF page',self.cli('freeze',run,ok=False)['error'])
        self.assertEqual(self.record(run)['status'],'SOURCE_REVIEW_REQUIRED')
        self.assertFalse((run/'preparation/target-selection.json').exists())
        self.assertEqual(self.runtime_calls(),[])

    def test_review_rejects_incomplete_duplicate_pages_and_false_attestations(self):
        run=self.begin();self.review(run);path=run/'preparation/source-review.json'
        original=json.loads(path.read_text())
        for change in [dict(checked_pages=[1]),dict(checked_pages=[1,1,2]),dict(checked_pages=[True,2]),
                       dict(source_only=False),dict(target_checked=False),dict(transcription_checked=False),
                       dict(source_sha256='0'*64),dict(schema='old'),dict(corrections='none'),
                       dict(corrections=[{'page':3,'detail':'outside page'}]),dict(notes=None)]:
            with self.subTest(change=change):
                path.write_text(json.dumps({**original,**change}))
                self.cli('freeze',run,ok=False)
                self.assertFalse((run/'preparation/target-selection.json').exists())
        self.assertEqual(self.runtime_calls(),[])

    def test_empty_or_foreign_symlinked_source_is_not_a_reviewed_input(self):
        run=self.begin();self.review(run)
        target=run/'preparation/target-statement.md';before=target.read_text();target.write_text(' ')
        self.assertIn('Complete the source-only file',self.cli('freeze',run,ok=False)['error'])
        target.write_text(before)
        checked=run/'preparation/checked-source.md';checked.unlink()
        old=self.base/'old-result.md';old.write_text('old benchmark material')
        checked.symlink_to(old)
        self.assertIn('symlinks',self.cli('freeze',run,ok=False)['error'])
        self.assertEqual(self.runtime_calls(),[])

    def test_extra_briefing_pages_or_mutated_startup_provenance_are_rejected(self):
        run=self.begin();self.review(run)
        for name in ['old-answer.md','pages/page-3.png']:
            path=run/'preparation'/name;path.write_text('extra historical input')
            with self.subTest(name=name):self.cli('freeze',run,ok=False)
            path.unlink()
        startup=run/'preparation/startup/settings.json';startup.write_text('{}')
        self.assertIn('Startup provenance changed',self.cli('freeze',run,ok=False)['error'])
        self.assertEqual(self.runtime_calls(),[])

    def test_legacy_result_directory_has_no_new_run_authority(self):
        previous=self.local/'results/old-benchmark';previous.mkdir(parents=True)
        (previous/'job.json').write_text('{"track":"full"}')
        value=self.cli('observe',previous,ok=False)
        self.assertIn('BENCHMARK_RUN.json',value['error'])
        self.assertEqual(self.runtime_calls(),[])

    def test_raw_source_and_rendered_evidence_must_remain_unchanged(self):
        run=self.begin();self.review(run)
        for name in ['original.pdf','extracted.md','pages/page-1.png']:
            path=run/'preparation'/name;before=path.read_bytes()
            with self.subTest(name=name):
                path.write_bytes(before+b'changed')
                self.assertIn('changed',self.cli('freeze',run,ok=False)['error'])
                path.write_bytes(before)
        self.assertEqual(self.runtime_calls(),[])

    def test_freeze_binds_the_exact_current_target_and_source(self):
        run=self.begin();self.review(run);target=run/'preparation/target-statement.md'
        self.assertEqual(self.cli('freeze',run)['status'],'INPUTS_FROZEN')
        selection=json.loads((run/'preparation/target-selection.json').read_text())
        self.assertEqual(selection['full_target'],target.read_text().strip())
        self.assertEqual(selection['document']['path'],str(run/'preparation/original.pdf'))
        self.assertEqual(selection['document']['sha256'],self.config['paper_sha256'])
        self.assertEqual(set(self.record(run)['reviewed_inputs']),{'checked-source.md','target-statement.md','source-review.json','target-selection.json'})
        self.cli('freeze',run,ok=False)
        self.assertEqual(self.runtime_calls(),[])

    def test_full_job_uses_only_three_bound_current_run_documents(self):
        run=self.prepared();job=json.loads((run/'workflow/job.json').read_text())
        self.assertEqual(self.record(run)['status'],'JOB_PREPARED')
        self.assertEqual(job['track'],'full');self.assertEqual(job['max_concurrency'],20)
        self.assertEqual(job['profiles'],self.config['profiles'])
        self.assertEqual(job['policy'],'normal')
        self.assertEqual([d['id'] for d in job['documents']],['problem.md','material-001.md','target-selection.json'])
        self.assertTrue(all(Path(d['original']['path']).is_relative_to(run/'preparation') for d in job['documents']))
        calls=self.runtime_calls();self.assertEqual([x[0] for x in calls],['prepare'])
        self.assertIn('--output',calls[0]);self.assertIn(str(run/'workflow'),calls[0])
        self.assertNotIn('--use-config-profiles',calls[0]);self.assertNotIn('--source',calls[0])

    def test_nl0_track_does_not_require_or_select_an_unused_lean_model(self):
        self.config['track']='nl0';self.config['profiles']['lean']['id']='unused-and-unavailable';self.save_config()
        run=self.begin();self.review(run);self.cli('freeze',run);self.cli('prepare',run)
        job=json.loads((run/'workflow/job.json').read_text())
        self.assertEqual(job['track'],'nl0')
        self.assertEqual(job['profiles']['lean'],job['profiles']['nl0'])
        self.launch(run);self.terminal(run)
        final=self.cli('finish',run)
        self.assertEqual(final['status'],'DRAFT-AUDIT-PASSED')
        self.assertEqual(final['bound_artifact_validation']['audit_b'],'NOT_AVAILABLE')
        self.assertFalse((run/'workflow/nl0-to-lean').exists())
        self.assertTrue(all(x[0] in {'prepare','execute','observe'} for x in self.runtime_calls()))

    def test_unexpected_jobs_and_imported_authority_are_rejected(self):
        for mode in ['extra_input','wrong_track','wrong_workers','wrong_profile','wrong_root','resume','wrong_target','foreign_source']:
            with self.subTest(mode=mode):
                run=self.begin(run_id=mode);self.review(run);self.cli('freeze',run)
                self.cli('prepare',run,ok=False,mode=mode)
                self.assertEqual(self.record(run)['status'],'JOB_PREPARATION_FAILED')
                self.assertTrue((run/'prepare-result.json').is_file())
                self.assertFalse((run/'dispatch-attempt.json').exists())
        self.assertTrue(all(x[0]=='prepare' for x in self.runtime_calls()))

    def test_prepare_failure_and_invalid_json_keep_actual_diagnostics(self):
        for mode in ['prepare_exit','bad_json','json_list']:
            with self.subTest(mode=mode):
                run=self.begin(run_id=mode);self.review(run);self.cli('freeze',run)
                self.cli('prepare',run,ok=False,mode=mode)
                self.assertEqual(self.record(run)['status'],'JOB_PREPARATION_FAILED')
                log=json.loads((run/'prepare-result.json').read_text())
                self.assertTrue(log['stdout'] or log['stderr'])
                self.cli('prepare',run,ok=False)
        self.assertEqual(len(self.runtime_calls()),3)

    def test_mutated_frozen_input_blocks_prepare_without_calling_yui(self):
        run=self.begin();self.review(run);self.cli('freeze',run)
        for name in ['checked-source.md','target-statement.md','source-review.json','target-selection.json']:
            path=run/'preparation'/name;before=path.read_bytes()
            with self.subTest(name=name):
                path.write_bytes(before+b' changed')
                self.assertIn('Frozen reviewed input changed',self.cli('prepare',run,ok=False)['error'])
                path.write_bytes(before)
        self.assertEqual(self.runtime_calls(),[])

    def test_verification_timestamps_change_without_invalidating_preparation(self):
        run=self.begin();self.review(run)
        before=self.record(run)['environment']['resolved_environment']['observed_at_utc']
        check=self.cli('check')
        self.assertNotEqual(check['environment']['resolved_environment']['observed_at_utc'],before)
        self.cli('freeze',run)
        self.assertEqual(self.record(run)['status'],'INPUTS_FROZEN')
        changed=json.loads(json.dumps(check['environment']))
        changed['resolved_environment']['synthetic_metadata']=False
        self.assertNotEqual(prepare_yui.environment_identity(changed),prepare_yui.environment_identity(check['environment']))

    def test_stale_settings_entry_runtime_and_original_block_launch(self):
        run=self.prepared()
        paths=[self.local/'settings.json',self.local/'README.md',self.install/'nl02lean/scripts/workflow.py',self.local/self.config['paper']]
        for path in paths:
            before=path.read_bytes()
            with self.subTest(path=path.name):
                if path.name=='settings.json':
                    config=dict(self.config,workers=21);path.write_text(json.dumps(config))
                else:path.write_bytes(before+b'\nchanged')
                self.launch(run,ok=False)
                self.assertFalse((run/'dispatch-attempt.json').exists())
                path.write_bytes(before)
        self.assertEqual([x[0] for x in self.runtime_calls()],['prepare'])

    def test_job_and_job_input_mutation_block_before_dispatch(self):
        run=self.prepared()
        job=run/'workflow/job.json';before=job.read_text()
        data=json.loads(before);data['unexpected']='change';job.write_text(json.dumps(data))
        self.assertIn('job changed',self.launch(run,ok=False)['error'])
        job.write_text(before)
        material=run/'workflow/inputs/material-001.md';material.write_text('changed')
        self.assertIn('job input changed',self.launch(run,ok=False)['error'])
        self.assertEqual([x[0] for x in self.runtime_calls()],['prepare'])

    def test_frozen_runtime_mutation_blocks_execution_and_observation(self):
        run=self.prepared();path=run/'workflow/runtime/nl0/scripts/yui.py';path.write_text('raise SystemExit(99)')
        self.assertIn('frozen runtime changed',self.launch(run,ok=False)['error'])
        self.assertIn('frozen runtime changed',self.cli('observe',run,ok=False)['error'])
        self.assertEqual([x[0] for x in self.runtime_calls()],['prepare'])

    def test_existing_workflow_cannot_be_overwritten(self):
        run=self.begin();self.review(run);self.cli('freeze',run)
        (run/'workflow').mkdir();(run/'workflow/sentinel').write_text('keep')
        self.assertIn('overwrite',self.cli('prepare',run,ok=False)['error'])
        self.assertEqual((run/'workflow/sentinel').read_text(),'keep')
        self.assertEqual(self.runtime_calls(),[])

    def test_launch_requires_a_heartbeat_before_any_dispatch_attempt(self):
        run = self.prepared()
        error = self.cli('launch', run, ok=False)['error']
        self.assertIn('--heartbeat-id', error)
        self.assertEqual([call[0] for call in self.runtime_calls()], ['prepare'])
        self.assertFalse((run/'dispatch-attempt.json').exists())

    def test_launch_is_one_detached_call_and_cannot_be_repeated(self):
        run=self.prepared();value=self.launch(run)
        self.assertEqual(value['status'],'DISPATCHED')
        state = json.loads((run/'OWNER_MONITOR_STATE.json').read_text())
        self.assertEqual(state['automation_id'], 'fixture-heartbeat')
        self.assertEqual(state['target_thread_id'], 'fixture-owner')
        self.assertEqual(state['runs'], [str(run/'workflow')])
        self.assertEqual(state['observe_command'][-3:], [str(self.local/'prepare_yui.py'), 'observe', str(run)])
        self.assertEqual(value['owner_observation']['notifications'], 'every_wake')
        self.assertEqual(value['owner_observation']['registration'], 'RECORDED_BY_OWNER')
        self.launch(run,ok=False);self.cli('prepare',run,ok=False)
        calls=self.runtime_calls();self.assertEqual([x[0] for x in calls],['prepare','execute'])
        self.assertEqual(calls[-1],['execute',str(run/'workflow'),'--detach'])
        self.assertEqual(self.record(run)['status'],'DISPATCHED')
        self.assertIsNone(self.record(run)['model_started'])

    def test_retained_dispatch_attempt_blocks_a_second_call_even_if_state_is_prepared(self):
        run=self.prepared()
        (run/'dispatch-attempt.json').write_text('{"attempt":"already reserved"}')
        self.launch(run,ok=False)
        self.assertEqual([x[0] for x in self.runtime_calls()],['prepare'])
        self.assertIn('already reserved',(run/'dispatch-attempt.json').read_text())

    def test_launch_fault_or_missing_identity_preserves_attempt_and_never_retries(self):
        for mode in ['execute_exit','missing_identity']:
            with self.subTest(mode=mode):
                run=self.prepared();self.launch(run,ok=False,mode=mode)
                self.assertEqual(self.record(run)['status'],'DISPATCH_ERROR')
                self.assertTrue((run/'dispatch-attempt.json').exists())
                self.assertTrue((run/'dispatch-result.json').exists())
                self.launch(run,ok=False)
        self.assertEqual(sum(x[0]=='execute' for x in self.runtime_calls()),2)

    def test_json_process_retains_partial_timeout_output(self):
        log=self.base/'timeout.json'
        error=subprocess.TimeoutExpired(['synthetic'],.01,output=b'partial stdout',stderr=b'partial stderr')
        with patch.object(prepare_yui.subprocess,'run',side_effect=error):
            with self.assertRaises(subprocess.TimeoutExpired):
                prepare_yui.json_process(['synthetic'],timeout=.01,log=log)
        value=json.loads(log.read_text())
        self.assertIsNone(value['exit_code']);self.assertEqual(value['stdout'],'partial stdout')
        self.assertEqual(value['stderr'],'partial stderr')

    def test_observation_is_bounded_and_writes_only_owner_log(self):
        run=self.prepared();self.launch(run)
        before=(run/'workflow/job.json').read_bytes()
        value=self.cli('observe',run)
        self.assertFalse(value['all_terminal'])
        self.assertEqual((run/'workflow/job.json').read_bytes(),before)
        self.assertEqual(len((run/'OWNER_MONITOR_LOG.jsonl').read_text().splitlines()),1)
        self.assertEqual([x[0] for x in self.runtime_calls()],['prepare','execute','observe'])

    def test_cancel_preserves_evidence_blocks_launch_and_is_not_terminal_itself(self):
        run=self.prepared();before=(run/'workflow/job.json').read_bytes()
        self.assertEqual(self.cli('cancel',run)['status'],'CANCEL_REQUESTED')
        self.assertEqual((run/'workflow/job.json').read_bytes(),before)
        self.assertEqual(self.record(run)['status'],'CANCEL_REQUESTED')
        self.launch(run,ok=False)
        self.cli('finish',run,ok=False)
        self.assertFalse((run/'FINAL_OUTCOME.json').exists())
        self.terminal(run,'CANCELLED')
        final=self.cli('finish',run)
        self.assertEqual(final['status'],'CANCELLED')
        self.assertIsNone(final['timing']['launch_started_at_utc'])

    def test_observation_from_another_workflow_cannot_supply_exit_evidence(self):
        run=self.prepared();self.launch(run);self.terminal(run)
        value=self.cli('observe',run,ok=False,mode='foreign_observation')
        self.assertIn('exact workflow map',value['error'])
        self.assertFalse((run/'OWNER_MONITOR_LOG.jsonl').exists())
        self.assertFalse((run/'FINAL_OUTCOME.json').exists())

    def test_live_paused_or_unverified_process_exit_cannot_finish(self):
        run=self.prepared();self.launch(run)
        self.cli('finish',run,ok=False)
        self.terminal(run)
        for name in ['paused.json','still-live.json']:
            path=run/'workflow'/name;path.write_text('{}')
            with self.subTest(name=name):
                self.assertIn('Not ready',self.cli('finish',run,ok=False)['error'])
                self.assertFalse((run/'FINAL_OUTCOME.json').exists())
            path.unlink()
        self.assertEqual(self.record(run)['status'],'DISPATCHED')

    def test_finish_validates_bound_existing_evidence_and_preserves_partial_usage(self):
        run=self.prepared();self.launch(run);self.terminal(run)
        stage=run/'workflow/nl0-to-lean/workers/T001';stage.mkdir(parents=True)
        (stage/'result.json').write_text(json.dumps({'execution_health':'FAULT','measurement_valid':False}))
        final=self.cli('finish',run)
        self.assertEqual(final['status'],'WORKFLOW-PASSED')
        self.assertEqual(final['usage'],{'status':'PARTIAL','confirmed_tokens':123})
        self.assertFalse(final['bound_artifact_validation']['mathematics_automatically_verified'])
        self.assertEqual(final['stage_execution_health'][0]['execution_health'],'FAULT')
        self.assertGreaterEqual(final['timing']['preparation_wall_seconds'],0)
        self.assertGreaterEqual(final['timing']['total_to_terminal_record_seconds'],final['timing']['preparation_wall_seconds'])
        self.assertEqual(self.record(run)['status'],'FINALIZED')
        self.cli('finish',run,ok=False)
        self.assertTrue(all(x[0] in {'prepare','execute','observe'} for x in self.runtime_calls()))

    def test_conditional_outcome_is_never_promoted(self):
        run=self.prepared();self.launch(run);self.terminal(run,'WORKFLOW-CONDITIONAL')
        receipt=run/'workflow/synthetic-machine-acceptance.json'
        receipt.write_text(json.dumps({'status':'AUDIT-B-CONDITIONAL','source_conditional':True}))
        final=self.cli('finish',run)
        self.assertEqual(final['status'],'WORKFLOW-CONDITIONAL')
        self.assertTrue(final['bound_artifact_validation']['audit_b']['source_conditional'])

    def test_forged_job_binding_or_invalid_receipt_prevents_final_acceptance(self):
        run=self.prepared();self.launch(run);self.terminal(run)
        case=run/'workflow/case-result.json';data=json.loads(case.read_text());original=case.read_text()
        data['job']['sha256']='0'*64;case.write_text(json.dumps(data))
        self.assertIn('not bound',self.cli('finish',run,ok=False)['error'])
        case.write_text(original)
        receipt=run/'workflow/synthetic-machine-acceptance.json';receipt.write_text('{"status":"NOT_PASSED"}')
        self.assertIn('invalid synthetic receipt',self.cli('finish',run,ok=False)['error'])
        self.assertFalse((run/'FINAL_OUTCOME.json').exists())

    def test_final_receipt_outside_own_run_is_rejected(self):
        run=self.prepared();self.launch(run);self.terminal(run)
        case=run/'workflow/case-result.json';data=json.loads(case.read_text())
        data['result']['audit_b']['receipt_path']=str(self.base/'old-result.json')
        case.write_text(json.dumps(data))
        self.assertIn('outside this run',self.cli('finish',run,ok=False)['error'])
        self.assertFalse((run/'FINAL_OUTCOME.json').exists())

    def test_terminal_predicate_rejects_inconsistent_or_malformed_snapshots(self):
        valid={'all_terminal':True,'all_process_exits_verified':True,'process_inspection_error':None,
               'cases':[{'phase':'FINISHED','terminal_record_present':True,'process_exit_verified':True,
                         'paused_errors':[],'live_owned_process_count':0,'registered_groups_still_present':[]}]}
        self.assertTrue(prepare_yui.terminal_ready(valid))
        for change in [dict(all_terminal=False),dict(all_process_exits_verified=False),
                       dict(process_inspection_error='unavailable'),dict(cases=[]),dict(cases=None),dict(cases=[None])]:
            with self.subTest(change=change):self.assertFalse(prepare_yui.terminal_ready({**valid,**change}))
        for change in [dict(phase='PAUSED_ERROR'),dict(counts={'PAUSED_ERROR':1}),dict(paused_errors=None),
                       dict(paused_errors=[{'incident':'pending'}]),dict(live_owned_process_count=True),
                       dict(live_owned_process_count=1),dict(registered_groups_still_present=[1]),
                       dict(process_exit_verified=False)]:
            with self.subTest(change=change):
                self.assertFalse(prepare_yui.terminal_ready({**valid,'cases':[{**valid['cases'][0],**change}]}))
        self.assertFalse(prepare_yui.terminal_ready(None))

    def test_owner_log_cannot_write_through_an_external_symlink(self):
        run=self.prepared();outside=self.base/'outside.jsonl';outside.write_text('keep')
        (run/'OWNER_MONITOR_LOG.jsonl').symlink_to(outside)
        self.assertIn('symlinks',self.cli('observe',run,ok=False)['error'])
        self.assertEqual(outside.read_text(),'keep')

    def test_metadata_write_refuses_symlink_and_preserves_existing_data(self):
        outside=self.base/'outside.json';outside.write_text('{"keep":true}')
        link=self.base/'link.json';link.symlink_to(outside)
        with self.assertRaisesRegex(ValueError,'symlink'):prepare_yui.write(link,{'overwrite':True})
        self.assertEqual(outside.read_text(),'{"keep":true}')
        with self.assertRaises(FileExistsError):prepare_yui.write(outside,{},exclusive=True)


if __name__=='__main__':unittest.main()
