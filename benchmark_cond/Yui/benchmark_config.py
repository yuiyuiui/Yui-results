"""The portable, Yui-only benchmark configuration and local path boundary."""
from __future__ import annotations

import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
NAME = 'Yui'
SKILL = 'rigorous-proof'
KEYS = {'schema_version', 'benchmark_name', 'skill_name', 'paper', 'paper_sha256',
        'target', 'target_label', 'track', 'policy', 'workers', 'profiles', 'limits',
        'runtime', 'preparation', 'results_directory', 'monitor', 'source_policy',
        'reuse_previous_results', 'formalization'}


def local_path(value, *, root=ROOT):
    if not isinstance(value, str) or not value.strip():
        raise ValueError('Benchmark paths must be nonempty local relative paths')
    path = Path(value)
    if path.is_absolute() or '..' in path.parts or not path.parts:
        raise ValueError('Benchmark paths must be nonempty local relative paths')
    base = Path(root).resolve()
    selected = base
    for part in path.parts:
        selected = selected / part
        if selected.is_symlink():
            raise ValueError('Benchmark paths may not use symlinks')
    if not selected.resolve().is_relative_to(base):
        raise ValueError('Benchmark path escapes its own directory')
    return selected


def load_config(root=ROOT):
    config = json.loads((Path(root) / 'settings.json').read_text())
    if not isinstance(config, dict) or set(config) != KEYS:
        raise ValueError('Use exactly the documented Yui settings fields')
    if config['schema_version'] != 'yui-benchmark-setup-2':
        raise ValueError('Unsupported Yui benchmark configuration')
    if config['benchmark_name'] != NAME or config['skill_name'] != SKILL:
        raise ValueError('This directory serves only the Yui rigorous-proof benchmark')
    if Path(root).name != NAME:
        raise ValueError('Keep the self-contained benchmark directory named Yui')
    if config['paper'] != 'aim-518-kdv-log-loss.pdf' or config['results_directory'] != 'results':
        raise ValueError('Use this directory\'s original paper and results directory')
    if not isinstance(config['paper_sha256'], str) or not re.fullmatch('[0-9a-f]{64}', config['paper_sha256']):
        raise ValueError('Bind the original paper with its SHA-256')
    if config['target_label'] != 'Theorem 1' or not isinstance(config['target'], str) or not config['target'].strip():
        raise ValueError('The complete Theorem 1 is required')
    if not isinstance(config['track'], str) or config['track'] not in {'full', 'nl0'} or config['policy'] != 'normal':
        raise ValueError('Choose full or nl0 with the normal repair policy')
    if not isinstance(config['formalization'],str) or config['formalization'] not in {'conditional','unconditional'}:
        raise ValueError('Choose explicit conditional or unconditional formalization')
    if config['formalization']=='unconditional' and config['track']!='full':
        raise ValueError('Unconditional formalization requires the full track')
    if type(config['workers']) is not int or config['workers'] < 1:
        raise ValueError('Configure a positive integer worker count')
    profiles = config['profiles']
    if not isinstance(profiles, dict) or set(profiles) != {'nl0', 'lean'}:
        raise ValueError('Configure both profile slots; an unused slot is not dispatched')
    for profile in profiles.values():
        if not isinstance(profile, dict) or set(profile) != {'id', 'reasoning_effort', 'speed', 'automatic_fallback'}:
            raise ValueError('Use complete explicit phase profiles')
        if any(not isinstance(profile[k], str) or not profile[k].strip() for k in ('id', 'reasoning_effort')):
            raise ValueError('A model and reasoning effort are required for each phase')
        if profile['speed'] != 'standard' or profile['automatic_fallback'] is not False:
            raise ValueError('Use Standard with no automatic model fallback')
    if not isinstance(config['limits'], dict) or type(config['limits'].get('native_seconds')) is not int or config['limits'] != dict(case_seconds=None, stage_seconds=None, tokens=None,
                               model_calls=None, native_seconds=180):
        raise ValueError('Keep unlimited total budgets and the 180-second native-call limit')
    runtime = config['runtime']
    if not isinstance(runtime, dict) or set(runtime) != {'expected_commit', 'expected_sha256'}:
        raise ValueError('Use explicit registered-runtime binding settings')
    for key, width in [('expected_commit', 40), ('expected_sha256', 64)]:
        value = runtime[key]
        if value is not None and (not isinstance(value, str) or not re.fullmatch('[0-9a-f]{'+str(width)+'}', value)):
            raise ValueError('Invalid runtime pin: '+key)
    prep = config['preparation']
    if not isinstance(prep, dict) or set(prep) != {'mode', 'render_dpi'} or prep['mode'] != 'source_only_full_paper':
        raise ValueError('Use the same source-only full-paper preparation in every run')
    if type(prep['render_dpi']) is not int or not 72 <= prep['render_dpi'] <= 300:
        raise ValueError('PDF rendering DPI must be an integer from 72 to 300')
    if not isinstance(config['monitor'], dict) or type(config['monitor'].get('interval_seconds')) is not int or config['monitor'] != dict(interval_seconds=600, foreground='end_turn_after_handoff',
                                 notifications='every_wake'):
        raise ValueError('Keep the bounded ten-minute host monitoring contract')
    if config['reuse_previous_results'] is not False:
        raise ValueError('Previous benchmark results are not construction inputs')
    if not isinstance(config['source_policy'], str) or not config['source_policy'].strip():
        raise ValueError('Retain the source-qualification policy')
    for key in ('paper', 'results_directory'):
        local_path(config[key], root=root)
    return config
