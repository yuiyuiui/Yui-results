"""Portable configuration and filesystem boundaries, using synthetic inputs."""
import copy
from pathlib import Path
import json
import unittest

from support import BENCHMARK, Fixture, benchmark_config


class ConfigurationTests(Fixture):
    def reject(self, change):
        value=copy.deepcopy(self.config)
        change(value)
        (self.local/'settings.json').write_text(json.dumps(value))
        with self.assertRaises(ValueError):benchmark_config.load_config(self.local)

    def test_checked_in_defaults_are_explicit(self):
        config=benchmark_config.load_config()
        self.assertEqual(config['benchmark_name'],'Yui')
        self.assertEqual(config['workers'],20)
        self.assertIn(config['track'],{'full','nl0'})
        self.assertEqual(config['policy'],'normal')
        self.assertFalse(config['reuse_previous_results'])
        self.assertEqual(set(config['profiles']),{'nl0','lean'})
        self.assertEqual(config['profiles']['nl0']['id'],'gpt-6.1-sol')

    def test_full_and_nl0_are_supported_without_prompt_overrides(self):
        for track in ('full','nl0'):
            self.config['track']=track;self.config['formalization']='conditional';self.save_config()
            self.assertEqual(benchmark_config.load_config(self.local)['track'],track)

    def test_schema_identity_missing_and_extra_settings_are_rejected(self):
        cases=[lambda d:d.update(schema_version='old'),lambda d:d.update(benchmark_name='benchmark'),
               lambda d:d.update(skill_name='rigorous-proof-development'),lambda d:d.pop('track'),
               lambda d:d.update(extra_instruction='use another skill')]
        for change in cases:
            with self.subTest(change=cases.index(change)):self.reject(change)

    def test_invalid_scope_target_and_reuse_are_rejected(self):
        for field,values in [('track',['translate','audit-b','',None,[]]),
                             ('policy',['first-pass',None]),('target_label',['Theorem 2',None]),
                             ('target',['',None]),('reuse_previous_results',[True,None,0])]:
            for value in values:
                with self.subTest(field=field,value=value):self.reject(lambda d:d.update({field:value}))

    def test_workers_must_be_positive_integers(self):
        for value in [True,False,0,-1,1.5,'20',None]:
            with self.subTest(value=value):self.reject(lambda d:d.update(workers=value))

    def test_profile_slots_and_fallback_cannot_be_implicit(self):
        cases=[lambda d:d.update(profiles={}),lambda d:d['profiles'].pop('lean'),
               lambda d:d['profiles']['nl0'].update(automatic_fallback=True),
               lambda d:d['profiles']['nl0'].update(speed='fast'),
               lambda d:d['profiles']['nl0'].update(id=''),
               lambda d:d['profiles']['lean'].update(reasoning_effort=None),
               lambda d:d['profiles']['nl0'].update(other='override')]
        for change in cases:
            with self.subTest(change=cases.index(change)):self.reject(change)

    def test_total_limits_native_limit_and_monitoring_are_fixed(self):
        cases=[lambda d:d['limits'].update(case_seconds=60),lambda d:d['limits'].update(tokens=1000),
               lambda d:d['limits'].update(model_calls=2),lambda d:d['limits'].update(native_seconds=300),
               lambda d:d['limits'].update(native_seconds=180.0),
               lambda d:d['monitor'].update(interval_seconds=1),lambda d:d['monitor'].update(interval_seconds=600.0),
               lambda d:d['monitor'].update(foreground='poll'),
               lambda d:d['monitor'].update(notifications='meaningful_changes_only')]
        for change in cases:
            with self.subTest(change=cases.index(change)):self.reject(change)

    def test_source_and_results_cannot_be_redirected_to_an_old_run(self):
        for field,value in [('paper','results/old/inputs/problem.md'),('paper','/old/paper.pdf'),
                            ('results_directory','../pure-model-result'),('paper_sha256','bad')]:
            with self.subTest(field=field,value=value):self.reject(lambda d:d.update({field:value}))

    def test_runtime_pin_format_and_preparation_contract_are_checked(self):
        for field,value in [('expected_commit','abc'),('expected_sha256','z'*64)]:
            self.reject(lambda d:d['runtime'].update({field:value}))
        for value in [True,0,71,301,'120']:
            with self.subTest(dpi=value):self.reject(lambda d:d['preparation'].update(render_dpi=value))
        self.reject(lambda d:d['preparation'].update(mode='optional_briefing'))
        self.reject(lambda d:d.update(source_policy=''))

    def test_local_paths_reject_empty_absolute_traversal_and_symlinks(self):
        for value in ['', '.', '../old', '/old', 'sub/../../old', None]:
            with self.subTest(value=value),self.assertRaises(ValueError):
                benchmark_config.local_path(value,root=self.local)
        (self.local/'alias').symlink_to(self.local,target_is_directory=True)
        with self.assertRaisesRegex(ValueError,'symlinks'):
            benchmark_config.local_path('alias/settings.json',root=self.local)
        self.assertEqual(benchmark_config.local_path('results/new',root=self.local),self.local/'results/new')

    def test_malformed_settings_and_wrong_container_are_rejected(self):
        (self.local/'settings.json').write_text('[]')
        with self.assertRaises(ValueError):benchmark_config.load_config(self.local)
        (self.local/'settings.json').write_text('{')
        with self.assertRaises(ValueError):benchmark_config.load_config(self.local)
        self.save_config()
        other=self.base/'different';other.mkdir()
        (other/'settings.json').write_text(json.dumps(self.config))
        with self.assertRaisesRegex(ValueError,'named Yui'):benchmark_config.load_config(other)

    def test_entry_assigns_every_current_item_a_role(self):
        text=(BENCHMARK/'README.md').read_text()
        for path in BENCHMARK.iterdir():
            if path.name=='__pycache__':continue
            with self.subTest(item=path.name):self.assertIn('`'+path.name+('/' if path.is_dir() else '')+'`',text)
        for path in (BENCHMARK/'tests').glob('*.py'):
            self.assertIn(path.name,text)
        self.assertNotIn('/Users/syyui',text)
        self.assertIn('single execution entry',text)
        self.assertIn('There is no `.prepared/task.md`',text)


if __name__=='__main__':unittest.main()
