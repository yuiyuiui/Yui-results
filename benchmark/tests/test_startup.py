"""Local startup, isolation and stale-preparation controls; no model or proof run."""
from contextlib import ExitStack
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

BENCHMARK = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCHMARK))
import benchmark_config
import prepare_yui
import skill_check as skills


class StartupTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.config = benchmark_config.load_config()
        self.name = self.config['skill_name']
        self.other = 'other-proof-skill'
        self.install = self.root / 'installed skill with spaces'
        for name in ['SKILL.md', 'config.json', 'nl0/scripts/yui.py',
                     'nl0/scripts/direct_runner.py', 'nl02lean/scripts/workflow.py', 'toolchain/lock.json']:
            p = self.install / name; p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text('---\nname: '+self.name+'\ndescription: Synthetic test only.\n---\n'
                         if name == 'SKILL.md' else '{}')
        self.entry = {'name': self.name, 'path': str(self.install / 'SKILL.md'),
                      'enabled': True, 'scope': 'user'}

    def tearDown(self):
        self.temp.cleanup()

    def registry(self, *entries):
        return {'data': [{'cwd': str(self.root), 'skills': list(entries), 'errors': []}]}

    def selected(self):
        return skills.select(self.registry(self.entry))

    def fake_codex(self):
        log = self.root / 'metadata calls.jsonl'; binary = self.root / 'fake codex'
        binary.write_text('#!/usr/bin/env python3\nimport json,sys\n'
            'registry='+repr(self.registry(self.entry))+'\n'
            'for line in sys.stdin:\n'
            ' value=json.loads(line)\n'
            ' with open('+repr(str(log))+',"a") as out: out.write(json.dumps(value)+"\\n")\n'
            ' if "id" not in value: continue\n'
            ' if value["method"] not in {"initialize","skills/list"}: raise SystemExit(99)\n'
            ' result=registry if value["method"]=="skills/list" else {}\n'
            ' print(json.dumps({"id":value["id"],"result":result}),flush=True)\n')
        binary.chmod(0o700)
        return binary, log

    def test_exact_enabled_name_and_no_variant_fallback(self):
        for entry in [{**self.entry, 'name': 'rigorous-proof-development'},
                      {**self.entry, 'name': self.other}]:
            with self.subTest(name=entry['name']), self.assertRaises(skills.SkillUnavailable):
                skills.select(self.registry(entry))
        with self.assertRaisesRegex(skills.SkillUnavailable, 'disabled'):
            skills.select(self.registry({**self.entry, 'enabled': False}))
        with patch.object(skills, 'inventory') as inventory:
            with self.assertRaisesRegex(skills.SkillUnavailable, 'exactly'):
                skills.require_skill(skill_name=self.other)
            inventory.assert_not_called()
        self.assertEqual(self.selected()['root'], str(self.install))

    def test_unregistered_neighbor_is_not_an_installation(self):
        sibling = self.root / 'Yui'; sibling.mkdir()
        (sibling / 'SKILL.md').write_text('---\nname: '+self.name+'\n---\n')
        with self.assertRaisesRegex(skills.SkillUnavailable, 'not installed'):
            skills.select(self.registry())

    def test_missing_runtime_and_wrong_frontmatter_block_startup(self):
        (self.install / 'nl0/scripts/yui.py').unlink()
        with self.assertRaisesRegex(skills.SkillUnavailable, 'incomplete'):
            self.selected()
        (self.install / 'SKILL.md').write_text('---\nname: rigorous-proof-development\n---\n')
        with self.assertRaisesRegex(skills.SkillUnavailable, 'exact '+self.name):
            self.selected()

    def test_alias_deduplication_and_duplicate_installation_rejection(self):
        alias = self.root / 'skill alias'; alias.symlink_to(self.install, target_is_directory=True)
        self.assertEqual(skills.select(self.registry(self.entry,
            {**self.entry, 'path': str(alias / 'SKILL.md')}))['root'], str(self.install))
        other = self.root / 'other installation'; shutil.copytree(self.install, other)
        with self.assertRaisesRegex(skills.SkillUnavailable, 'Several enabled'):
            skills.select(self.registry(self.entry, {**self.entry, 'path': str(other / 'SKILL.md')}))

    def test_registry_discovery_calls_no_thread_or_model_methods(self):
        binary, log = self.fake_codex()
        result = skills.require_skill(self.root, codex=binary)
        self.assertEqual(result['status'], 'INSTALLED_SKILL_VERIFIED')
        self.assertFalse(result['model_started'])
        self.assertEqual([json.loads(line)['method'] for line in log.read_text().splitlines()],
                         ['initialize', 'initialized', 'skills/list'])

    def test_only_local_folder_is_needed_after_relocation(self):
        local = self.root / 'isolated path with spaces' / BENCHMARK.name
        local.mkdir(parents=True)
        for name in prepare_yui.STARTUP_FILES:
            shutil.copyfile(BENCHMARK / name, local / name)
        binary, _ = self.fake_codex()
        result = subprocess.run([sys.executable, '-B', str(local / 'skill_check.py'),
                                 '--codex', str(binary)], cwd=self.root,
                                capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        self.assertEqual(json.loads(result.stdout)['name'], self.name)
        self.assertFalse((local / 'pure-model-result').exists())
        self.assertFalse((local.parent / 'another-benchmark').exists())

    def test_portable_contract_rejects_wrong_pair_and_escaping_paths(self):
        local = self.root / BENCHMARK.name; local.mkdir()
        config = dict(self.config, skill_name=self.other)
        (local / 'settings.json').write_text(json.dumps(config))
        with self.assertRaisesRegex(ValueError, 'do not match'):
            benchmark_config.load_config(local)
        for value in ['/some/host/path', '../sibling', '.']:
            with self.subTest(path=value), self.assertRaises(ValueError):
                benchmark_config.local_path(value, root=local)
        (local / 'outside link').symlink_to(self.root, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'escapes'):
            benchmark_config.local_path('outside link/result', root=local)

    def test_invocation_preserves_source_target_settings_and_full_gates(self):
        paper = self.root / 'original paper.pdf'; paper.write_bytes(b'%PDF synthetic')
        prompt = prepare_yui.invocation(paper, 20, self.selected())
        self.assertTrue(prompt.startswith('Use $'+self.name))
        for value in [str(paper), str(self.install / 'SKILL.md'), self.config['target'],
                      str(BENCHMARK / 'results'), 'gpt-6.1-sol / high / Standard',
                      'count is 20', '300-second', 'independent Audit B', '--detach',
                      'every 600 seconds', 'warn.json/warn.md', 'start authorization']:
            self.assertIn(value, prompt)
        self.assertNotIn('including the unfiltered method', prompt)
        self.assertNotIn(str(BENCHMARK.parent / 'test'), prompt)

    def test_wrong_worker_or_installed_variant_cannot_generate_a_prompt(self):
        paper = self.root / 'paper.pdf'; paper.write_bytes(b'%PDF synthetic')
        for n in [0, -1, True, 10]:
            with self.subTest(workers=n), self.assertRaises(ValueError):
                prepare_yui.invocation(paper, n, self.selected())
        with self.assertRaisesRegex(ValueError, 'exactly'):
            prepare_yui.invocation(paper, 20, dict(self.selected(), name=self.other))

    def test_cli_rejects_wrong_worker_before_registry_or_environment_work(self):
        with patch.object(prepare_yui, 'require_skill') as discover, patch('sys.stdout', new=io.StringIO()) as out:
            self.assertEqual(prepare_yui.main(['--workers', '10']), 1)
            discover.assert_not_called()
            self.assertEqual(json.loads(out.getvalue())['status'], 'BENCHMARK_NOT_STARTED')

    def sandbox(self, stack):
        local = self.root / 'portable copy' / BENCHMARK.name; local.mkdir(parents=True)
        for name in prepare_yui.STARTUP_FILES:
            shutil.copyfile(BENCHMARK / name, local / name)
        (local / self.config['paper']).write_bytes(b'%PDF synthetic')
        stack.enter_context(patch.object(prepare_yui, 'ROOT', local))
        stack.enter_context(patch.object(prepare_yui, 'PREPARED', local / '.prepared'))
        stack.enter_context(patch.object(prepare_yui, 'local_path',
            side_effect=lambda name: benchmark_config.local_path(name, root=local)))
        stack.enter_context(patch.object(prepare_yui, 'environment_check',
            return_value={'status': 'SYNTHETIC_READ_ONLY_CHECK', 'model_started': False}))
        return local

    def test_preparation_only_writes_local_metadata_and_no_result_job(self):
        with ExitStack() as stack:
            local = self.sandbox(stack)
            stack.enter_context(patch.object(prepare_yui, 'require_skill', return_value=self.selected()))
            out = stack.enter_context(patch('sys.stdout', new=io.StringIO()))
            self.assertEqual(prepare_yui.main(['--write-preparation']), 0)
            self.assertEqual(json.loads(out.getvalue())['status'], 'READY_AWAITING_USER_START')
            record = json.loads((local / '.prepared/readiness.json').read_text())
            self.assertFalse(record['model_started'])
            self.assertFalse(record['workflow_created'])
            self.assertFalse(record['start_authorized'])
            self.assertFalse((local / 'results').exists())
            self.assertEqual(prepare_yui.verify_preparation(self.selected(), self.config)['status'],
                             'PREPARATION_VALID_AWAITING_USER_START')

    def test_changed_paper_operator_instruction_runtime_or_task_invalidates_preparation(self):
        with ExitStack() as stack:
            local = self.sandbox(stack)
            record = prepare_yui.preparation(self.selected(), self.config)
            prepared = local / '.prepared'; prepared.mkdir()
            prompt = record.pop('prompt')
            (prepared / 'task.md').write_text(prompt)
            (prepared / 'readiness.json').write_text(json.dumps(record))
            for path in [local / self.config['paper'], local / 'README.md',
                         self.install / 'nl02lean/scripts/workflow.py', prepared / 'task.md']:
                original = path.read_bytes()
                with self.subTest(changed=str(path.relative_to(local) if path.is_relative_to(local) else 'runtime')):
                    try:
                        path.write_bytes(original + b'\nchanged')
                        with self.assertRaisesRegex(ValueError, 'stale'):
                            prepare_yui.verify_preparation(self.selected(), self.config)
                    finally:
                        path.write_bytes(original)
            with self.assertRaisesRegex(ValueError, 'stale'):
                prepare_yui.verify_preparation(self.selected(), dict(self.config, workers=21))


if __name__ == '__main__':
    unittest.main()
