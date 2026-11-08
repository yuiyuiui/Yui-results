"""Live entry/link checks, excluding immutable archived run documents."""
from pathlib import Path
import json
import re
import tomllib
import unittest
from urllib.parse import unquote,urlsplit

ROOT=Path(__file__).resolve().parents[2]
FAMILIES=('test_cond','test_uncond','test_uncond-test')
CASES=('geometry-product-dimension','lie-module-irreducibility','wave-map-energy')
EXERCISES=[ROOT/family/case/'README.md' for family in FAMILIES for case in CASES]
BENCHMARKS=[ROOT/'benchmark_cond/Yui/README.md']
ENTRIES=EXERCISES+BENCHMARKS


class EntryLayout(unittest.TestCase):
    def test_all_execution_entries_and_local_links_exist(self):
        discovered=set(ROOT.glob('test_*/*/README.md')) | set(ROOT.glob('benchmark_*/Yui/README.md'))
        self.assertEqual(discovered,set(ENTRIES))
        for path in ENTRIES:
            with self.subTest(entry=str(path.relative_to(ROOT))):
                text=path.read_text();self.assertIn('single execution entry',text)
                self.assertIn('CLEANUP.json',text);self.assertIn('FINAL_OUTCOME.json',text)
                self.assertIn('settings.json',text)
                script = 'run_test.py' if path in EXERCISES else 'prepare_yui.py'
                self.assertIn(f'python3 -B {script} launch RUN\n', text)
                self.assertIn('duration_ms=600000', text)
                self.assertIn('OWNER_CHAT_WAIT', text)
                self.assertIn('even when progress is', text)
                self.assertNotIn('end the turn before beginning', text)
                self.assertIn(f'python3 -B {script} launch RUN --heartbeat-id', text)
        pages=[ROOT/'README.md',ROOT/'benchmark_cond/README.md',
               ROOT/'benchmark_cond/pure-model-result/README.md',ROOT/'benchmark_cond/pure-model-result/REPRODUCE.md',*ENTRIES]
        for path in pages:
            text=path.read_text()
            headings={re.sub(r'[^a-z0-9\s-]','',line.lstrip('# ').lower()).replace(' ','-') for line in text.splitlines() if line.startswith('#')}
            for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)',text):
                parsed=urlsplit(target)
                if parsed.scheme:continue
                with self.subTest(page=str(path.relative_to(ROOT)),link=target):
                    if parsed.path:self.assertTrue((path.parent/unquote(parsed.path)).exists())
                    elif parsed.fragment:self.assertIn(parsed.fragment,headings)

    def test_all_entries_prefer_a_permitted_wakeup_and_continue_on_failure(self):
        procedures = []
        for path in ENTRIES:
            with self.subTest(entry=str(path.relative_to(ROOT))):
                body = path.read_text()
                start = body.index('### Choose the monitoring mode')
                end = body.index('\n## ', start)
                procedure = body[start:end].replace('prepare_yui.py', 'run_test.py')
                procedures.append(procedure)
                self.assertLess(procedure.index('Prefer a permitted ten-minute wakeup'),
                                procedure.index('Fallback when a wakeup cannot be established'))
                self.assertIn('restricted, unavailable, unsuccessful or unconfirmed', procedure)
                self.assertIn('continue with the same prepared run', procedure)
                self.assertIn('Run exactly one of the two launch commands', procedure)
                self.assertIn('end this foreground turn', procedure)
                self.assertIn('duration_ms=600000', procedure)
                self.assertIn('even when progress is unchanged', procedure)
                self.assertIn('RECORDED_BY_OWNER', procedure)
                self.assertIn('OWNER_CHAT_WAIT', procedure)
        self.assertTrue(all(body == procedures[0] for body in procedures))

    def test_all_entries_omit_worker_count(self):
        paths = sorted(ROOT.glob('test_*/*/settings.json')) + sorted(ROOT.glob('benchmark_*/Yui/settings.json'))
        self.assertEqual(set(paths),{entry.with_name('settings.json') for entry in ENTRIES})
        for path in paths:
            with self.subTest(entry=str(path.relative_to(ROOT))):
                self.assertNotIn('workers', json.loads(path.read_text()))

    def test_branch_comparison_preserves_every_input_and_isolates_its_results(self):
        revisions=set()
        for case in CASES:
            original=ROOT/'test_uncond'/case
            comparison=ROOT/'test_uncond-test'/case
            with self.subTest(case=case):
                for name in ('problem.md','run_test.py'):
                    self.assertEqual((comparison/name).read_bytes(),(original/name).read_bytes())
                before=json.loads((original/'settings.json').read_text())
                after=json.loads((comparison/'settings.json').read_text())
                pin=after.pop('yui_revision')
                self.assertEqual(pin['branch'],'uncond-test')
                self.assertRegex(pin['commit'],r'^[0-9a-f]{40}$')
                revisions.add(pin['commit'])
                self.assertEqual(after['limits'].pop('native_seconds'),360)
                self.assertEqual(before['limits'].pop('native_seconds'),180)
                self.assertEqual(after,before)
                readme=(comparison/'README.md').read_text()
                self.assertIn(f'Execute test_uncond-test/{case}/README.md',readme)
                self.assertNotIn('Execute test_uncond/',readme)
                self.assertEqual(after['results_directory'],'rigorous-proof')
                self.assertFalse((comparison/after['results_directory']).is_symlink())
        self.assertEqual(len(revisions),1)

    def test_foreground_defaults_match_all_worker_profiles(self):
        project = tomllib.loads((ROOT/'.codex/config.toml').read_text())
        self.assertEqual((project['model'], project['model_reasoning_effort'], project['service_tier']),
                         ('gpt-6.1-sol', 'high', 'default'))
        for pattern in ('test_*/*/settings.json', 'benchmark_*/Yui/settings.json'):
            for entry in ROOT.glob(pattern):
                with self.subTest(entry=entry):
                    settings = json.loads(entry.read_text())
                    for worker in settings['profiles'].values():
                        self.assertEqual((project['model'], project['model_reasoning_effort'], worker['speed']),
                                         (worker['id'], worker['reasoning_effort'], 'standard'))
                    self.assertEqual(settings['monitor'], {'interval_seconds':600,
                        'foreground':'wait_in_owner_chat', 'notifications':'every_wake'})

    def test_live_commands_use_current_paths_and_unconditional_has_no_bare_arm(self):
        for path in [ROOT/'README.md',ROOT/'benchmark_cond/pure-model-result/REPRODUCE.md',ROOT/'benchmark_cond/pure-model-result/prompt.py']:
            self.assertNotRegex(path.read_text(),r'(?<![\w-])(?:benchmark|test)/(?:Yui|pure-model-result|geometry-product|lie-module|wave-map)')
        self.assertFalse((ROOT/'benchmark_uncond/pure-model-result').exists())
        for family in FAMILIES:
            self.assertFalse((ROOT/family/'README.md').exists())
        for entry in BENCHMARKS:
            for helper in ('owner_monitor.py','resource_cleanup.py'):
                self.assertEqual((entry.parent/helper).read_bytes(),(ROOT/'entry_support'/helper).read_bytes())


if __name__=='__main__':unittest.main()
