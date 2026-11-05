"""Live entry/link checks, excluding immutable archived run documents."""
from pathlib import Path
import json
import re
import tomllib
import unittest
from urllib.parse import unquote,urlsplit

ROOT=Path(__file__).resolve().parents[2]


class EntryLayout(unittest.TestCase):
    def test_all_eight_execution_entries_and_local_links_exist(self):
        exercises=[p/'README.md' for family in ('test_cond','test_uncond') for p in (ROOT/family).iterdir() if p.is_dir()]
        benchmarks=[ROOT/family/'Yui/README.md' for family in ('benchmark_cond','benchmark_uncond')]
        self.assertEqual(len(exercises),6)
        for path in exercises+benchmarks:
            with self.subTest(entry=str(path.relative_to(ROOT))):
                text=path.read_text();self.assertIn('single execution entry',text)
                self.assertIn('CLEANUP.json',text);self.assertIn('FINAL_OUTCOME.json',text)
                self.assertIn('settings.json',text)
                script = 'run_test.py' if path in exercises else 'prepare_yui.py'
                self.assertIn(f'python3 -B {script} launch RUN\n', text)
                self.assertIn('duration_ms=600000', text)
                self.assertIn('OWNER_CHAT_WAIT', text)
                self.assertIn('even when progress is', text)
                self.assertNotIn('end the turn before beginning', text)
                self.assertIn(f'python3 -B {script} launch RUN --heartbeat-id', text)
        pages=[ROOT/'README.md',ROOT/'benchmark_cond/README.md',ROOT/'benchmark_uncond/README.md',
               ROOT/'benchmark_cond/pure-model-result/README.md',ROOT/'benchmark_cond/pure-model-result/REPRODUCE.md',*exercises,*benchmarks]
        for path in pages:
            text=path.read_text()
            headings={re.sub(r'[^a-z0-9\s-]','',line.lstrip('# ').lower()).replace(' ','-') for line in text.splitlines() if line.startswith('#')}
            for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)',text):
                parsed=urlsplit(target)
                if parsed.scheme:continue
                with self.subTest(page=str(path.relative_to(ROOT)),link=target):
                    if parsed.path:self.assertTrue((path.parent/unquote(parsed.path)).exists())
                    elif parsed.fragment:self.assertIn(parsed.fragment,headings)

    def test_all_eight_entries_prefer_a_permitted_wakeup_and_continue_on_failure(self):
        entries = sorted(ROOT.glob('test_*/*/README.md')) + sorted(ROOT.glob('benchmark_*/Yui/README.md'))
        self.assertEqual(len(entries), 8)
        procedures = []
        for path in entries:
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

    def test_foreground_defaults_match_all_eight_worker_profiles(self):
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
        self.assertFalse((ROOT/'test_cond/README.md').exists());self.assertFalse((ROOT/'test_uncond/README.md').exists())
        for family in ('benchmark_cond','benchmark_uncond'):
            self.assertEqual((ROOT/family/'Yui/owner_monitor.py').read_bytes(), (ROOT/'entry_support/owner_monitor.py').read_bytes())
        self.assertEqual((ROOT/'benchmark_cond/Yui/resource_cleanup.py').read_bytes(),(ROOT/'entry_support/resource_cleanup.py').read_bytes())
        self.assertEqual((ROOT/'benchmark_uncond/Yui/resource_cleanup.py').read_bytes(),(ROOT/'entry_support/resource_cleanup.py').read_bytes())


if __name__=='__main__':unittest.main()
