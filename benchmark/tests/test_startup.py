"""Independent benchmark startup controls; no model or Lean execution."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

BENCHMARK = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCHMARK))
import prepare_yui
import skill_check as skills


class StartupTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name).resolve()
        self.install = self.root/'installed skill with spaces'
        for name in ['SKILL.md', 'config.json', 'nl0/scripts/yui.py',
                     'nl0/scripts/direct_runner.py', 'nl02lean/scripts/workflow.py', 'toolchain/lock.json']:
            path = self.install/name; path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('---\nname: rigorous-proof\ndescription: Synthetic test only.\n---\n'
                            if name == 'SKILL.md' else '{}')
        self.entry = {'name': 'rigorous-proof', 'path': str(self.install/'SKILL.md'),
                      'enabled': True, 'scope': 'user'}

    def tearDown(self):
        self.temp.cleanup()

    def registry(self, *entries):
        return {'data': [{'cwd': str(self.root), 'skills': list(entries), 'errors': []}]}

    def test_exact_enabled_installed_name_is_required(self):
        with self.assertRaises(skills.SkillUnavailable):
            skills.select(self.registry({**self.entry, 'name': 'rigorous-proof-development'}))
        with self.assertRaisesRegex(skills.SkillUnavailable, 'disabled'):
            skills.select(self.registry({**self.entry, 'enabled': False}))
        self.assertEqual(skills.select(self.registry(self.entry))['root'], str(self.install))

    def test_unregistered_neighbor_checkout_is_not_an_installation(self):
        sibling = self.root/'Yui'; sibling.mkdir()
        (sibling/'SKILL.md').write_text('---\nname: rigorous-proof\n---\n')
        with self.assertRaisesRegex(skills.SkillUnavailable, 'not installed'):
            skills.select(self.registry())

    def test_missing_runtime_or_wrong_frontmatter_blocks_startup(self):
        (self.install/'nl0/scripts/yui.py').unlink()
        with self.assertRaisesRegex(skills.SkillUnavailable, 'incomplete'):
            skills.select(self.registry(self.entry))
        (self.install/'SKILL.md').write_text('---\nname: rigorous-proof-development\n---\n')
        with self.assertRaisesRegex(skills.SkillUnavailable, 'exact rigorous-proof'):
            skills.select(self.registry(self.entry))

    def test_duplicate_aliases_deduplicate_but_different_installations_are_ambiguous(self):
        alias = self.root/'skill alias'; alias.symlink_to(self.install, target_is_directory=True)
        self.assertEqual(skills.select(self.registry(self.entry,
            {**self.entry, 'path': str(alias/'SKILL.md')}))['root'], str(self.install))
        other = self.root/'other installation'
        import shutil
        shutil.copytree(self.install, other)
        with self.assertRaisesRegex(skills.SkillUnavailable, 'Several enabled'):
            skills.select(self.registry(self.entry, {**self.entry, 'path': str(other/'SKILL.md')}))

    def test_discovery_calls_only_initialize_and_skills_list(self):
        log = self.root/'metadata-calls.jsonl'; binary = self.root/'fake codex'
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
        result = skills.require_skill(self.root, codex=binary)
        self.assertEqual(result['status'], 'INSTALLED_SKILL_VERIFIED')
        self.assertFalse(result['model_started'])
        methods = [json.loads(line)['method'] for line in log.read_text().splitlines()]
        self.assertEqual(methods, ['initialize', 'initialized', 'skills/list'])

    def test_yui_invocation_is_explicit_and_uses_the_discovered_entry(self):
        paper = self.root/'paper.pdf'; paper.write_bytes(b'%PDF-1.7\nsynthetic')
        installed = skills.select(self.registry(self.entry))
        prompt = prepare_yui.invocation(paper, 10, installed)
        self.assertTrue(prompt.startswith('Use $rigorous-proof'))
        self.assertIn(str(self.install/'SKILL.md'), prompt)
        self.assertIn(str(paper), prompt)
        self.assertIn('10, for local R reviews', prompt)
        for count in (0, -1, True):
            with self.subTest(count=count), self.assertRaises(ValueError):
                prepare_yui.invocation(paper, count, installed)

    def test_direct_runner_resolves_only_the_registered_supervisor(self):
        source = self.install/'nl0/scripts/direct_runner.py'
        source.write_text('from pathlib import Path\n'
            'def main(**kwargs):\n'
            ' return {"supervisor":str(Path(__file__).resolve()),"args":kwargs["argv"]}\n')
        path = BENCHMARK/'pure-model-result/runner.py'
        sys.path.insert(0, str(path.parent))
        try:
            spec = importlib.util.spec_from_file_location('benchmark_direct_startup_control', path)
            module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
            with patch.object(module, 'require_skill', return_value=skills.select(self.registry(self.entry))):
                result = module.main(['--prepare-only'])
        finally:
            sys.path.remove(str(path.parent))
        self.assertEqual(result['supervisor'], str(source))
        self.assertEqual(result['args'], ['--prepare-only'])


if __name__ == '__main__':
    unittest.main()
