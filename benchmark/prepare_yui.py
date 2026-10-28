#!/usr/bin/env python3
"""Prepare an explicit installed-skill invocation; do not start a benchmark."""
import argparse
import json
from pathlib import Path

from skill_check import require_skill


def invocation(paper, workers, installed, *, model='gpt-6.1-sol', effort='high'):
    paper=Path(paper).expanduser().resolve()
    if not paper.is_file():
        raise FileNotFoundError('Supply an existing paper PDF')
    if type(workers) is not int or workers < 1:
        raise ValueError('Supply an explicitly confirmed positive worker count')
    return f'''Use $rigorous-proof for the full normal-policy workflow.

The installed skill was checked through Codex skills/list. Read its actual entry:
{installed['skill_md']}
Use that installed skill and its bundled runtime; do not look for a neighboring
Yui repository or invoke rigorous-proof-development.

Original paper: {paper}
Target: the complete Theorem 1, including the unfiltered method defined in the
paper and all standing definitions, hypotheses, quantifiers and parameter ranges.
Read the source and freeze the complete target under the skill's own rules.
Produce NL0, independent Audit A, Lean proofs, standalone assembly/native trust
inspection, and independent Audit B. Both phase profiles are {model} / {effort} /
Standard with no fallback. The explicitly selected per-case worker count is
{workers}, for local R reviews and later local Lean proofs in separate phases.
There is no imposed total time, token or call budget.

Use fresh output under this benchmark's rigorous-proof-result directory, outside
the installed skill. Do not read the direct arm or previous test outputs as
mathematical inputs. Preserve exact source qualifications and actual costs.
Follow the installed foreground handoff: detach the owned work, verify process
identities, register the host's ten-minute heartbeat, record its actual ID, then
end the foreground turn. Report a scheduling limitation if the host has no such
tool; do not replace it with a foreground polling loop.
'''


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--codex',type=Path)
    parser.add_argument('--paper',type=Path,default=Path(__file__).resolve().parent/'aim-518-kdv-log-loss.pdf')
    parser.add_argument('--workers',type=int,required=True)
    args=parser.parse_args(argv)
    try:
        installed=require_skill(codex=args.codex)
        prompt=invocation(args.paper,args.workers,installed)
    except (OSError,ValueError) as error:
        print(json.dumps({'status':'BENCHMARK_NOT_STARTED','error':str(error)}));return 1
    print(json.dumps({'status':'READY_FOR_SKILL_INVOCATION','model_started':False,
        'skill':{'name':installed['name'],'path':installed['skill_md']},'prompt':prompt},indent=2))
    return 0


if __name__=='__main__':
    raise SystemExit(main())
