"""Opt-in real Yui prepare API against a neutral PDF; never dispatches a job."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from support import benchmark_config, prepare_yui


def neutral_pdf(path):
    content=b'BT /F1 12 Tf 72 720 Td (Theorem 1. Synthetic software fixture only.) Tj ET\n'
    objects=[b'<< /Type /Catalog /Pages 2 0 R >>',
             b'<< /Type /Pages /Kids [3 0 R] /Count 1 >>',
             b'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 612 792] /Resources << /Font << /F1 4 0 R >> >> /Contents 5 0 R >>',
             b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>',
             b'<< /Length '+str(len(content)).encode()+b' >>\nstream\n'+content+b'endstream']
    data=b'%PDF-1.4\n';offsets=[0]
    for n,obj in enumerate(objects,1):
        offsets.append(len(data));data+=str(n).encode()+b' 0 obj\n'+obj+b'\nendobj\n'
    xref=len(data);data+=b'xref\n0 6\n0000000000 65535 f \n'
    for offset in offsets[1:]:data+=f'{offset:010d} 00000 n \n'.encode()
    data+=b'trailer\n<< /Size 6 /Root 1 0 R >>\nstartxref\n'+str(xref).encode()+b'\n%%EOF\n'
    path.write_bytes(data)


@unittest.skipUnless(os.environ.get('YUI_TEST_INSTALLATION'),
                     'Run after check with YUI_TEST_INSTALLATION=<registered root>; prepare only, no model')
class InstalledRuntimeContractTests(unittest.TestCase):
    def test_real_adapter_begin_freeze_prepare_handles_fresh_environment_timestamps(self):
        installed=Path(os.environ['YUI_TEST_INSTALLATION']).expanduser().resolve(strict=True)
        with tempfile.TemporaryDirectory(prefix='yui-neutral-adapter-') as temp:
            local=Path(temp).resolve()/'Yui';local.mkdir()
            for name in prepare_yui.STARTUP_FILES:
                shutil.copyfile(prepare_yui.ROOT/name,local/name)
            config=benchmark_config.load_config();config['track']='nl0';config['formalization']='conditional'
            pdf=local/config['paper'];neutral_pdf(pdf)
            config['paper_sha256']=prepare_yui.sha256(pdf)
            (local/'settings.json').write_text(json.dumps(config))
            entry={'name':'rigorous-proof','root':str(installed),
                   'skill_md':str(installed/'SKILL.md'),
                   'skill_sha256':prepare_yui.sha256(installed/'SKILL.md')}
            def local_path(value,*,root=local):return benchmark_config.local_path(value,root=root)
            with patch.object(prepare_yui,'ROOT',local),patch.object(prepare_yui,'local_path',side_effect=local_path),patch.object(prepare_yui,'load_config',return_value=config),patch.object(prepare_yui,'require_skill',return_value=entry):
                run=Path(prepare_yui.begin()['run']);prep=run/'preparation'
                (prep/'target-statement.md').write_text('Synthetic software fixture only.')
                review=prepare_yui.read(prep/'source-review.json')
                review.update(checked_pages=[1],transcription_checked=True,target_checked=True,source_only=True,
                              notes='Known one-page software fixture; not a mathematical benchmark.')
                prepare_yui.write(prep/'source-review.json',review)
                self.assertEqual(prepare_yui.freeze(run)['status'],'INPUTS_FROZEN')
                self.assertEqual(prepare_yui.prepare(run)['status'],'JOB_PREPARED')
                self.assertEqual(prepare_yui.validate_job(run,{'configuration':config})['track'],'nl0')
                self.assertFalse((run/'dispatch-attempt.json').exists())
                self.assertFalse((run/'workflow/execution-status.json').exists())

    def test_real_prepare_full_and_nl0_match_adapter_without_execution(self):
        installed=Path(os.environ['YUI_TEST_INSTALLATION']).expanduser().resolve(strict=True)
        with tempfile.TemporaryDirectory(prefix='yui-neutral-contract-') as temp:
            for track,mode in (('full','conditional'),('nl0','conditional'),('full','unconditional')):
                with self.subTest(track=track,mode=mode):
                    run=Path(temp).resolve()/(track+'-'+mode);prep=run/'preparation';prep.mkdir(parents=True)
                    pdf=prep/'original.pdf';neutral_pdf(pdf)
                    config=benchmark_config.load_config();config['track']=track;config['formalization']=mode
                    tools={name:shutil.which(name) for name in ('pdftotext','pdfinfo','pdftoppm')}
                    self.assertTrue(tools['pdfinfo'] and tools['pdftoppm'],'Install the documented PDF rendering tools')
                    count,exports=prepare_yui.extract_source(pdf,prep,config,tools,{'root':str(installed)})
                    self.assertEqual(count,1)
                    self.assertIn('original.pdf',exports)
                    self.assertEqual(len(list((prep/'pages').glob('page-*.png'))),1)
                    checked=prep/'checked-source.md'
                    self.assertIn('Synthetic software fixture only',checked.read_text())
                    program='''import json,sys
from pathlib import Path
root=Path(sys.argv[1]);pdf=Path(sys.argv[2]);sys.path.insert(0,str(root/'nl0/scripts'))
from target_selection import select
print(json.dumps(select(pdf,[{'id':'theorem-1','label':'Theorem 1','statement':'Synthetic software fixture only.','start_line':None}])))
'''
                    target=prepare_yui.runtime_program({'root':str(installed)},program,str(pdf))
                    (prep/'target-selection.json').write_text(json.dumps(target))
                    command=[sys.executable,'-B',str(installed/'nl0/scripts/yui.py'),'prepare',str(pdf),
                             '--track',track,'--formalization',mode,'--policy','normal','--max-concurrency',str(config['workers']),
                             '--material',str(checked),'--target-file',str(prep/'target-selection.json'),
                             '--output',str(run/'workflow')]
                    for phase in ('nl0','lean'):
                        for flag,key in [('model','id'),('effort','reasoning_effort'),('speed','speed')]:
                            command+=['--'+phase+'-'+flag,config['profiles'][phase][key]]
                    result=subprocess.run(command,capture_output=True,text=True,timeout=90)
                    self.assertEqual(result.returncode,0,result.stdout+result.stderr)
                    self.assertEqual(json.loads(result.stdout)['status'],'PREPARED_NOT_STARTED')
                    job=prepare_yui.validate_job(run,{'configuration':config})
                    self.assertEqual(job['track'],track)
                    self.assertTrue((run/'workflow/runtime/nl0/scripts/yui.py').is_file())
                    for name in ['launch.json','execution-status.json','case-result.json']:
                        self.assertFalse((run/'workflow'/name).exists(),name)


if __name__=='__main__':unittest.main()
