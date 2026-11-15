"""Current registry discovery must not require a retired scientific version pin."""
from importlib.util import module_from_spec,spec_from_file_location
from pathlib import Path
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=spec_from_file_location('current_entry_skill_check',ROOT/'skill_check.py')
discovery=module_from_spec(spec);spec.loader.exec_module(discovery)


class CurrentDiscovery(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='current-yui-discovery-')
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name).resolve()
        for name in ('config.json','nl0/scripts/yui.py','nl0/scripts/entrypoint.py',
                     'nl0/scripts/target_selection.py','nl0/scripts/nl0.py',
                     'nl02lean/scripts/workflow.py','nl02lean/scripts/final_acceptance.py',
                     'nl0/scripts/runtime_config.py'):
            path=self.root/name;path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text('{}' if path.suffix=='.json' else '')
        (self.root/'SKILL.md').write_text('---\nname: rigorous-proof\ndescription: Discovery fixture.\n---\n')
        self.registry={'data':[{'skills':[{'name':'rigorous-proof','enabled':True,
            'path':str(self.root/'SKILL.md'),'scope':'user'}],'errors':[]}]}

    def test_current_installation_needs_no_fixed_toolchain_lock(self):
        self.assertFalse((self.root/'toolchain/lock.json').exists())
        self.assertEqual(discovery.select(self.registry)['root'],str(self.root))

    def test_missing_runtime_configuration_still_rejects_incomplete_installation(self):
        (self.root/'nl0/scripts/runtime_config.py').unlink()
        with self.assertRaisesRegex(discovery.SkillUnavailable,'incomplete'):
            discovery.select(self.registry)


if __name__=='__main__':unittest.main()
