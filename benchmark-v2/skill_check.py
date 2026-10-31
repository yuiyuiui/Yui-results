#!/usr/bin/env python3
"""Resolve this benchmark's exact installed skill through Codex's registry.

Only initialize and skills/list are called. No thread, model turn or benchmark
is started, and no neighboring checkout is used as an installation fallback.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import queue
import re
import shutil
import subprocess
import threading
import time

from benchmark_config import load_config

NAME = load_config()['skill_name']
SUPPORTED_NAMES = {'rigorous-proof', 'rigorous-proof-v2'}


class SkillUnavailable(ValueError):
    pass


def codex_binary(explicit=None):
    selected = explicit or os.environ.get('YUI_CODEX_BINARY')
    candidates = [selected] if selected else [shutil.which('codex'),
        '/Applications/Codex.app/Contents/Resources/codex',
        '/Applications/ChatGPT.app/Contents/Resources/codex-cli/CodexCLI.app/Contents/MacOS/codex']
    for item in candidates:
        if item and Path(item).expanduser().is_file():
            return Path(item).expanduser().resolve()
    raise SkillUnavailable('Codex is unavailable; configure YUI_CODEX_BINARY or put codex on PATH')


def inventory(cwd, *, codex=None, timeout=30):
    binary = codex_binary(codex)
    messages = queue.Queue()
    process = subprocess.Popen([str(binary), 'app-server', '--stdio'], cwd=Path(cwd),
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
        text=True, bufsize=1)

    def read():
        for line in process.stdout:
            try:
                messages.put(json.loads(line))
            except json.JSONDecodeError:
                continue
        messages.put(None)

    reader = threading.Thread(target=read, daemon=True); reader.start()
    try:
        def rpc(number, method, params):
            process.stdin.write(json.dumps({'id': number, 'method': method, 'params': params})+'\n')
            process.stdin.flush(); deadline = time.monotonic()+timeout
            while True:
                try:
                    message = messages.get(timeout=max(0, deadline-time.monotonic()))
                except queue.Empty as error:
                    raise SkillUnavailable('Codex skill discovery timed out; no model was started') from error
                if message is None:
                    raise SkillUnavailable('Codex closed before returning its skill registry')
                if message.get('id') != number:
                    continue
                if 'error' in message:
                    raise SkillUnavailable('Codex skill discovery failed: '+str(message['error']))
                return message.get('result', {})
        rpc(1, 'initialize', {'clientInfo': {'name': 'yui-benchmark-preflight', 'version': '1'},
                             'capabilities': {'experimentalApi': True}})
        process.stdin.write(json.dumps({'method': 'initialized'})+'\n'); process.stdin.flush()
        result = rpc(2, 'skills/list', {'cwds': [str(Path(cwd).resolve())], 'forceReload': True})
        return binary, result
    finally:
        process.stdin.close()
        try:
            process.wait(timeout=3)
        except subprocess.TimeoutExpired:
            process.terminate()
            try:
                process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                process.kill(); process.wait()
        reader.join(timeout=1)
        process.stdout.close()


def select(result, *, skill_name=NAME):
    if skill_name not in SUPPORTED_NAMES:
        raise SkillUnavailable('Select an explicit supported Yui skill: '+', '.join(sorted(SUPPORTED_NAMES)))
    candidates = {}
    disabled = False
    for group in result.get('data', []):
        for item in group.get('skills', []):
            if item.get('name') != skill_name:
                continue
            if item.get('enabled') is not True:
                disabled = True
                continue
            path = Path(item['path']).expanduser()
            if not path.is_absolute():
                raise SkillUnavailable('Codex returned a nonabsolute installed skill path')
            path = path.resolve()
            if path.is_dir():
                path = path/'SKILL.md'
            if not path.is_file():
                raise SkillUnavailable('The registered rigorous-proof entry is missing: '+str(path))
            header = path.read_text().split('---', 2)
            match = re.search(r'^name:\s*[\"\']?([^\"\'\n]+?)[\"\']?\s*$',
                              header[1] if len(header) >= 3 else '', re.MULTILINE)
            if not match or match.group(1).strip() != skill_name:
                raise SkillUnavailable('The registered entry is not the exact '+skill_name+' skill')
            root = path.parent
            required = ['config.json', 'nl0/scripts/yui.py', 'nl0/scripts/direct_runner.py',
                        'nl02lean/scripts/workflow.py', 'toolchain/lock.json']
            if any(not (root/name).is_file() for name in required):
                raise SkillUnavailable('The installed rigorous-proof skill is incomplete: '+str(root))
            candidates[path] = {'name': skill_name, 'skill_md': str(path), 'root': str(root),
                'scope': item.get('scope'), 'skill_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
    if not candidates:
        state = 'disabled' if disabled else 'not installed'
        raise SkillUnavailable('Required skill $'+skill_name+' is '+state+
            '. Install/enable the complete Yui skill, then retry. A sibling Yui checkout is not an installation.')
    if len(candidates) != 1:
        raise SkillUnavailable('Several enabled '+skill_name+' installations were found; resolve the duplicate names before starting')
    return next(iter(candidates.values()))


def require_skill(cwd=None, *, codex=None, skill_name=NAME):
    if skill_name != NAME:
        raise SkillUnavailable('This benchmark requires exactly $'+NAME+'; no variant substitution')
    binary, result = inventory(cwd or Path(__file__).resolve().parent, codex=codex)
    return {'status': 'INSTALLED_SKILL_VERIFIED', **select(result, skill_name=skill_name),
            'codex': str(binary), 'resolved_by': 'codex_skills_list', 'model_started': False}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--codex', type=Path)
    parser.add_argument('--skill', choices=[NAME], default=NAME)
    args = parser.parse_args(argv)
    try:
        result = require_skill(codex=args.codex, skill_name=args.skill)
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(json.dumps({'status': 'BENCHMARK_NOT_STARTED', 'error': str(error)}))
        return 1
    print(json.dumps(result, indent=2)); return 0


if __name__ == '__main__':
    raise SystemExit(main())
