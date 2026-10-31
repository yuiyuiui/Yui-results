"""Compatibility of the retained direct runner; excluded from the V2 benchmark."""
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

BENCHMARK = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCHMARK))


class DirectStartupTests(unittest.TestCase):
    def test_direct_runner_still_loads_only_the_registered_supervisor(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve(); source = root / 'nl0/scripts/direct_runner.py'
            source.parent.mkdir(parents=True)
            source.write_text('from pathlib import Path\n'
                'def main(**kwargs):\n'
                ' return {"supervisor":str(Path(__file__).resolve()),"args":kwargs["argv"]}\n')
            path = BENCHMARK / 'pure-model-result/runner.py'
            sys.path.insert(0, str(path.parent))
            try:
                spec = importlib.util.spec_from_file_location('direct_startup_compatibility', path)
                module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
                with patch.object(module, 'require_skill', return_value={'root': str(root)}):
                    result = module.main(['--prepare-only'])
            finally:
                sys.path.remove(str(path.parent))
            self.assertEqual(result['supervisor'], str(source))
            self.assertEqual(result['args'], ['--prepare-only'])


if __name__ == '__main__':
    unittest.main()
