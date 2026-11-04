"""Live entry/link checks, excluding immutable archived run documents."""
from pathlib import Path
import re
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

    def test_live_commands_use_current_paths_and_unconditional_has_no_bare_arm(self):
        for path in [ROOT/'README.md',ROOT/'benchmark_cond/pure-model-result/REPRODUCE.md',ROOT/'benchmark_cond/pure-model-result/prompt.py']:
            self.assertNotRegex(path.read_text(),r'(?<![\w-])(?:benchmark|test)/(?:Yui|pure-model-result|geometry-product|lie-module|wave-map)')
        self.assertFalse((ROOT/'benchmark_uncond/pure-model-result').exists())
        self.assertFalse((ROOT/'test_cond/README.md').exists());self.assertFalse((ROOT/'test_uncond/README.md').exists())
        self.assertEqual((ROOT/'benchmark_cond/Yui/resource_cleanup.py').read_bytes(),(ROOT/'entry_support/resource_cleanup.py').read_bytes())
        self.assertEqual((ROOT/'benchmark_uncond/Yui/resource_cleanup.py').read_bytes(),(ROOT/'entry_support/resource_cleanup.py').read_bytes())


if __name__=='__main__':unittest.main()
