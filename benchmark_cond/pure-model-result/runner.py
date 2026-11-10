#!/usr/bin/env python3
"""Load only the direct supervisor from the enabled installed Yui skill."""
import argparse
import importlib.util
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from skill_check import require_skill
from prompt import render


def main(argv=None):
    argv=sys.argv[1:] if argv is None else argv
    parser=argparse.ArgumentParser(add_help=False);parser.add_argument('--codex',type=Path)
    known,_=parser.parse_known_args(argv)
    installed=require_skill(codex=known.codex)
    source=Path(installed['root'])/'nl0/scripts/direct_runner.py'
    spec=importlib.util.spec_from_file_location('installed_yui_direct_supervisor',source)
    supervisor=importlib.util.module_from_spec(spec);spec.loader.exec_module(supervisor)
    # The measured direct session receives only render(), not the Yui skill.
    return supervisor.main(default_work=Path(__file__).resolve().parent,prompt_factory=render,
        default_paper=Path(__file__).resolve().parent/'aim-518-kdv-log-loss.pdf',argv=argv)


if __name__=='__main__':
    try:
        main()
    except (OSError,ValueError) as error:
        import json
        print(json.dumps({'status':'BENCHMARK_NOT_STARTED','error':str(error)}));raise SystemExit(1)
