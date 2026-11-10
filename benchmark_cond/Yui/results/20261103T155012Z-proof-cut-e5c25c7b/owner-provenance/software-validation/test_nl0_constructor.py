"""Constructor rule delivery and fault boundaries; no live model execution."""
import harness_support
import errno
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import clean_stage
from clean_stage import ArtifactStage
from controller_common import CORE, bind, manifest
import nl0_author
import remote_retry
import runtime_snapshot


RULE = Path('nl0/references/nl0_constructor.md')


class ConstructorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.core = self.root/'installation'
        for relative in [Path('SKILL.md'), Path('config.json'), Path('toolchain/lock.json'),
                         Path('nl0/references/audit-a.md'),
                         Path('nl0/templates/authoring.md'), RULE]:
            target = self.core/relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((CORE/relative).read_bytes())
        self.rule = self.core/RULE
        self.original = self.rule.read_text()
        inputs = self.root/'inputs'
        inputs.mkdir()
        (inputs/'problem.md').write_text('For real a=b, prove a+0=b.')
        manifest(inputs)
        self.prepared = nl0_author.prepare(inputs, self.root/'prepared')
        self.stages = []

    def tearDown(self):
        for stage in self.stages:
            if hasattr(stage, 'work'):
                stage.release_resources('USER_CANCELLED')
                shutil.rmtree(stage.work, ignore_errors=True)
        self.temp.cleanup()

    def stage(self, *, kind='nl0'):
        stage = ArtifactStage.__new__(ArtifactStage)
        self.stages.append(stage)
        with patch.object(clean_stage, 'CORE', self.core):
            stage.__init__(self.root/f'stage-{len(self.stages)}',
                (self.prepared/'prompt.txt').read_text(), phase='nl0-author',
                kind=kind, inputs=self.prepared/'inputs/inputs.json', library=False)
        return stage

    def read(self, stage, **arguments):
        with patch.object(clean_stage, 'CORE', self.core):
            return stage.dispatch('read_yui', {'path': str(RULE), 'start': 1,
                                             'end': 250, **arguments})

    def test_author_reads_exact_frozen_rule_after_installation_edit(self):
        stage = self.stage()
        self.rule.write_text('A later installation revision must not reach this stage.')
        result = self.read(stage)
        returned = '\n'.join(line.split(': ', 1)[1] for line in result['text'].splitlines())
        self.assertEqual(returned, self.original.rstrip('\n'))
        self.assertFalse(result['has_more'])
        self.assertIsNone(stage.accepted)
        self.assertEqual(stage.api_calls, 0)

    def test_bad_read_arguments_are_rejected_without_poisoning_the_next_read(self):
        stage = self.stage()
        for arguments in [{'start': 0}, {'start': 4, 'end': 2},
                          {'path': '../../private.md'}, {'path': 'tests/private.md'}]:
            with self.subTest(arguments=arguments):
                result = self.read(stage, **arguments)
                self.assertFalse(result['accepted'])
                self.assertEqual(result['feedback_kind'], 'candidate_rejected')
                self.assertIsNone(stage.accepted)
        self.assertEqual(self.read(stage)['total_lines'], len(self.original.splitlines()))
        self.assertFalse(getattr(stage, 'tool_execution_fault', None))

    def test_missing_constructor_blocks_author_before_model_work(self):
        self.rule.unlink()
        with self.assertRaisesRegex(FileNotFoundError, 'constructor') as raised:
            self.stage()
        self.assertEqual(remote_retry.diagnose(raised.exception)['category'], 'harness_bug')
        self.assertFalse(remote_retry.diagnose(raised.exception)['retryable'])
        self.assertEqual(self.stages[-1].api_calls, 0)

    def test_empty_constructor_blocks_author_before_model_work(self):
        self.rule.write_text(' \n\t\n')
        with self.assertRaisesRegex(ValueError, 'constructor') as raised:
            self.stage()
        self.assertEqual(remote_retry.diagnose(raised.exception)['category'], 'harness_bug')
        self.assertFalse(remote_retry.diagnose(raised.exception)['retryable'])

    def test_unreadable_rule_is_not_accepted_as_missing_mathematical_evidence(self):
        original_read = Path.read_text

        def fail(path, *args, **kwargs):
            if path == self.rule:
                raise PermissionError(errno.EACCES, 'Synthetic unreadable constructor')
            return original_read(path, *args, **kwargs)

        with patch.object(Path, 'read_text', fail):
            with self.assertRaises(PermissionError):
                self.stage()

    def test_reader_execution_fault_is_retained_and_propagated(self):
        stage = self.stage()
        with patch.object(clean_stage, 'read_page',
                          side_effect=OSError(errno.EIO, 'Synthetic rule-reader I/O fault')):
            with self.assertRaises(OSError):
                self.read(stage)
        result = json.loads((stage.logs/'tools.jsonl').read_text().splitlines()[-1])['result']
        self.assertEqual(result['feedback_kind'], 'tool_execution_fault')
        self.assertFalse(result['retryable'])
        self.assertFalse(result['stage_complete'])
        self.assertEqual(result['tool'], 'read_yui')
        self.assertIsNone(stage.accepted)

    def test_snapshot_preserves_module_and_rejects_tampering_or_removal(self):
        run = self.root/'run'
        run.mkdir()
        rows = [bind(path) for path in sorted(self.core.rglob('*')) if path.is_file()]
        descriptor, bindings, catalog = runtime_snapshot.capture(run, rows, core=self.core)
        job = dict(root=str(run), runtime_snapshot=descriptor, runtime=bindings,
                   library_catalog=catalog)
        frozen = run/'runtime'/RULE
        self.rule.write_text('Changed installation')
        runtime_snapshot.validate(job)
        self.assertEqual(frozen.read_text(), self.original)
        frozen.write_text('Changed owned module')
        with self.assertRaises(ValueError):
            runtime_snapshot.validate(job)
        frozen.write_text(self.original)
        frozen.unlink()
        with self.assertRaises(ValueError):
            runtime_snapshot.validate(job)

    def test_json_review_stage_does_not_gain_an_author_only_requirement(self):
        self.rule.unlink()
        stage = self.stage(kind='json')
        result = self.read(stage)
        self.assertFalse(result['accepted'])
        self.assertEqual(result['feedback_kind'], 'candidate_rejected')
        self.assertEqual(stage.api_calls, 0)


if __name__ == '__main__':
    unittest.main()
