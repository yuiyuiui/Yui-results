"""Real local registry-protocol and environment subprocesses, never a model."""
from pathlib import Path
import json
import os
import shutil
from unittest.mock import patch
import unittest

from support import Fixture, prepare_yui, skill_check


class DiscoveryTests(Fixture):
    def select(self,*entries):
        return skill_check.select({'data':[{'skills':list(entries),'errors':[]}]})

    def test_exact_enabled_registration_and_no_neighbor_fallback(self):
        self.assertEqual(self.select(self.entry)['root'],str(self.install))
        for name in ['rigorous-proof-development','another-proof-skill']:
            with self.subTest(name=name),self.assertRaises(skill_check.SkillUnavailable):
                self.select({**self.entry,'name':name})
        with self.assertRaisesRegex(skill_check.SkillUnavailable,'not installed'):self.select()
        with self.assertRaisesRegex(skill_check.SkillUnavailable,'disabled'):
            self.select({**self.entry,'enabled':False})
        with patch.object(skill_check,'inventory') as discover:
            with self.assertRaisesRegex(skill_check.SkillUnavailable,'exactly'):
                skill_check.require_skill(skill_name='another-proof-skill')
            discover.assert_not_called()

    def test_alias_deduplication_and_ambiguous_installation_rejection(self):
        alias=self.base/'alias';alias.symlink_to(self.install,target_is_directory=True)
        self.assertEqual(self.select(self.entry,{**self.entry,'path':str(alias/'SKILL.md')})['root'],str(self.install))
        other=self.base/'other installation';shutil.copytree(self.install,other)
        with self.assertRaisesRegex(skill_check.SkillUnavailable,'Several enabled'):
            self.select(self.entry,{**self.entry,'path':str(other/'SKILL.md')})

    def test_missing_entry_bad_header_and_missing_runtime_are_rejected(self):
        path=self.install/'SKILL.md';original=path.read_text()
        for content in ['no header','---\nname: wrong\n---\n']:
            path.write_text(content)
            with self.assertRaisesRegex(skill_check.SkillUnavailable,'exact rigorous-proof'):self.select(self.entry)
        path.write_text(original)
        script=self.install/'nl0/scripts/yui.py';script.unlink()
        with self.assertRaisesRegex(skill_check.SkillUnavailable,'incomplete'):self.select(self.entry)
        path.unlink()
        with self.assertRaisesRegex(skill_check.SkillUnavailable,'missing'):self.select(self.entry)

    def test_relative_missing_paths_and_malformed_registry_fail_closed(self):
        for entry in [{**self.entry,'path':'relative/SKILL.md'},{**self.entry,'path':None},
                      {**self.entry,'path':''}]:
            with self.subTest(entry=entry),self.assertRaises(skill_check.SkillUnavailable):self.select(entry)
        for registry in [None,[],{}, {'data':None},{'data':[None]},
                         {'data':[{'skills':[],'errors':['incomplete']}]},
                         {'data':[{'skills':[None]}]}]:
            with self.subTest(registry=registry),self.assertRaises(skill_check.SkillUnavailable):
                skill_check.select(registry)

    def test_registry_protocol_has_only_initialize_and_skills_list(self):
        value=self.cli('check')
        self.assertFalse(value['model_started'])
        self.assertEqual([json.loads(x)['method'] for x in self.registry_calls.read_text().splitlines()],
                         ['initialize','initialized','skills/list'])
        self.assertEqual(self.runtime_calls(),[])
        self.assertFalse((self.local/'results').exists())
        self.assertFalse((self.local/'.prepared').exists())

    def test_rpc_error_closed_pipe_and_timeout_are_explicit(self):
        for behavior in ('error','close'):
            self.write_codex(behavior)
            with self.subTest(behavior=behavior),self.assertRaises((skill_check.SkillUnavailable,OSError)):
                skill_check.inventory(self.local,codex=self.binary,timeout=.1)
        self.write_codex('hang')
        with self.assertRaisesRegex(skill_check.SkillUnavailable,'timed out'):
            skill_check.inventory(self.local,codex=self.binary,timeout=.03)

    def test_explicit_missing_binary_does_not_fall_back(self):
        with patch.dict(os.environ,{'YUI_CODEX_BINARY':str(self.base/'not-installed')}):
            with self.assertRaisesRegex(skill_check.SkillUnavailable,'unavailable'):skill_check.codex_binary()

    def test_policy_drift_authentication_and_environment_fault_block_before_run(self):
        runtime=self.install/'config.json';original=runtime.read_text()
        for change in [dict(case_seconds=60),dict(native_seconds=300)]:
            data=json.loads(original);data['timeouts'].update(change);runtime.write_text(json.dumps(data))
            value=self.cli('check',ok=False)
            self.assertIn('policy differs',value['error'])
        data=json.loads(original);data['token_budget']=1000;runtime.write_text(json.dumps(data))
        self.assertIn('policy differs',self.cli('check',ok=False)['error'])
        runtime.write_text(original)
        self.assertIn('toolchain mismatch',self.cli('check',ok=False,mode='bad_environment')['error'])
        (self.install/'auth/auth.json').unlink()
        self.assertIn('authentication',self.cli('check',ok=False)['error'])
        self.assertFalse((self.local/'results').exists())
        self.assertEqual(self.runtime_calls(),[])

    def test_unknown_model_and_effort_do_not_fall_back(self):
        for field,value in [('id','unavailable-model'),('reasoning_effort','unavailable-effort')]:
            original=dict(self.config['profiles']['nl0'])
            self.config['profiles']['nl0'][field]=value;self.save_config()
            self.assertIn('unavailable',self.cli('check',ok=False)['error'])
            self.config['profiles']['nl0']=original
        self.assertEqual(self.runtime_calls(),[])

    def test_source_hash_and_runtime_pin_fail_before_model_dispatch(self):
        binding=prepare_yui.runtime_binding({'root':str(self.install)})
        self.assertIsNone(binding['source_commit'])
        self.assertIsNone(binding['dirty'])
        paper=self.local/self.config['paper'];original=paper.read_bytes();paper.write_bytes(original+b'changed')
        self.assertIn('hash mismatch',self.cli('check',ok=False)['error'])
        self.assertFalse(self.registry_calls.exists())
        paper.write_bytes(original)
        self.config['runtime']['expected_commit']='0'*40;self.save_config()
        self.assertIn('expected_commit',self.cli('check',ok=False)['error'])
        self.config['runtime']={'expected_commit':None,'expected_sha256':'0'*64};self.save_config()
        self.assertIn('expected_sha256',self.cli('check',ok=False)['error'])
        self.assertEqual(self.runtime_calls(),[])

    def test_relocated_copy_uses_no_sibling_benchmark_or_fixed_user_path(self):
        value=self.cli('check')
        self.assertEqual(value['installed']['root'],str(self.install))
        self.assertFalse((self.local.parent/'pure-model-result').exists())
        self.assertFalse((self.local.parent/'benchmark_config.py').exists())
        self.assertFalse((self.local/'results').exists())


if __name__=='__main__':unittest.main()
