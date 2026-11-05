"""Bind a detached entry to the heartbeat its owning chat registered with the host."""
import json
import os
from pathlib import Path
import shlex
import sys


def record_monitor(heartbeat_id, run, entry, policy, *, write):
    if not isinstance(heartbeat_id, str) or not heartbeat_id.strip():
        raise ValueError('Register a ten-minute heartbeat in this chat and pass its returned --heartbeat-id before launch')
    chat = os.environ.get('CODEX_THREAD_ID') or os.environ.get('YUI_OWNER_THREAD_ID')
    if not chat:
        raise ValueError('Launch from the owning chat with its thread ID available')
    workflow = run / 'workflow'
    owner = workflow / 'owner-context.json'
    if owner.is_symlink():
        raise ValueError('Refusing a symlink for the workflow owner record')
    if owner.is_file():
        recorded = json.loads(owner.read_text())
        if not isinstance(recorded, dict) or recorded.get('thread_id') != chat:
            raise ValueError('The prepared workflow belongs to a different owner chat')
    entry = Path(entry).resolve()
    command = [sys.executable, '-B', str(entry), 'observe', str(run)]
    monitor = {
        **policy,
        'automation_id': heartbeat_id.strip(),
        'target_thread_id': chat,
        'runs': [str(workflow)],
        'registration': 'RECORDED_BY_OWNER',
        'observe_command': command,
        'prompt': (
            f'Observe the existing run with {shlex.join(command)} once per wake. '
            'Post a short Chinese status in this chat on every wake, including unchanged progress. '
            f'Follow the fault and terminal instructions in {entry.with_name("README.md")}. '
            'End each foreground turn between wakes.'
        ),
        'next_action': 'Verify the detached controller once, post the initial status, then end this foreground turn.',
    }
    path = run / 'OWNER_MONITOR_STATE.json'
    state = {'schema': 'yui-owner-monitor-state-1', 'status': 'ACTIVE', **monitor}
    try:
        write(path, state, exclusive=True)
    except FileExistsError:
        # An interruption may have saved this receipt before the dispatch attempt.
        if path.is_symlink() or not path.is_file():
            raise ValueError('Expected a local owner monitor receipt')
        existing = json.loads(path.read_text())
        if not isinstance(existing, dict) or any(existing.get(k) != v for k, v in state.items()):
            raise ValueError('A different heartbeat is already recorded for this run')
    return monitor
