"""Portable local benchmark contract; no sibling-directory dependencies."""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SKILLS = {'benchmark': 'rigorous-proof'}


def local_path(value, *, root=ROOT):
    relative = Path(value)
    if relative.is_absolute() or '..' in relative.parts or not relative.parts:
        raise ValueError('Benchmark paths must be nonempty local relative paths')
    selected = (Path(root) / relative).resolve()
    if not selected.is_relative_to(Path(root).resolve()):
        raise ValueError('Benchmark path escapes its own directory')
    return selected


def load_config(root=ROOT):
    config = json.loads((Path(root) / 'settings.json').read_text())
    if config.get('schema_version') != 'yui-benchmark-setup-1':
        raise ValueError('Unsupported benchmark configuration')
    if SKILLS.get(config.get('benchmark_name')) != config.get('skill_name'):
        raise ValueError('Benchmark name and exact required skill do not match')
    if Path(root).name != config['benchmark_name']:
        raise ValueError('Use the configuration belonging to this benchmark directory')
    if type(config.get('workers')) is not int or config['workers'] < 1:
        raise ValueError('An explicitly selected positive worker count is required')
    expected = dict(id='gpt-6.1-sol', reasoning_effort='high', speed='standard', automatic_fallback=False)
    if config.get('profiles') != {'nl0': expected, 'lean': expected}:
        raise ValueError('Both benchmark phases must retain gpt-6.1-sol/high/Standard without fallback')
    if config.get('track') != 'full' or config.get('policy') != 'normal':
        raise ValueError('Use the full normal-policy benchmark')
    if config.get('limits') != dict(case_seconds=None, stage_seconds=None, tokens=None,
                                    model_calls=None, native_seconds=180):
        raise ValueError('Keep unlimited total budgets and the 180-second native-call limit')
    if config.get('monitor') != dict(interval_seconds=600, foreground='end_turn_after_handoff',
                                     notifications='meaningful_changes_only'):
        raise ValueError('Keep the detached ten-minute monitoring contract')
    if config.get('reuse_previous_results') is not False or not config.get('target'):
        raise ValueError('A complete target and fresh execution are required')
    for key in ['paper', 'results_directory']:
        local_path(config[key], root=root)
    return config
