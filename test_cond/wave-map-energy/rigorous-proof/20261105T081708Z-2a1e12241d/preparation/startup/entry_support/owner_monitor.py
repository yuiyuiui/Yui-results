"""Bind one detached run to its owner and to the observation mode actually used."""
import json
import os
from pathlib import Path
import shlex
import sys


def validate_monitor(policy):
    if (not isinstance(policy, dict)
            or set(policy) != {'interval_seconds', 'foreground', 'notifications'}
            or type(policy['interval_seconds']) is not int or policy['interval_seconds'] != 600
            or policy['foreground'] not in ('wait_in_owner_chat', 'end_turn_after_handoff')
            or policy['notifications'] != 'every_wake'):
        raise ValueError('Use the configured ten-minute owner reports')


def record_monitor(heartbeat_id, run, entry, policy, *, write):
    validate_monitor(policy)
    in_chat = heartbeat_id is None and policy['foreground'] == 'wait_in_owner_chat'
    if not in_chat and (not isinstance(heartbeat_id, str) or not heartbeat_id.strip()):
        raise ValueError('A scheduled handoff needs a genuine nonempty --heartbeat-id')
    chat = os.environ.get('CODEX_THREAD_ID') or os.environ.get('YUI_OWNER_THREAD_ID')
    if not chat:
        raise ValueError('Launch from the owning chat with its thread ID available')
    workflow = run / 'workflow'
    owner = workflow / 'owner-context.json'
    if owner.is_symlink():
        raise ValueError('Refusing a symlink for the workflow owner record')
    if in_chat and not owner.is_file():
        raise ValueError('Missing prepared workflow owner for in-chat observation')
    if owner.is_file():
        recorded = json.loads(owner.read_text())
        if not isinstance(recorded, dict) or recorded.get('thread_id') != chat:
            raise ValueError('The prepared workflow belongs to a different owner chat')
    entry = Path(entry).resolve()
    command = [sys.executable, '-B', str(entry), 'observe', str(run)]
    monitor = {
        **policy,
        'target_thread_id': chat,
        'runs': [str(workflow)],
        'observe_command': command,
    }
    if in_chat:
        monitor.update({
            'registration': 'OWNER_CHAT_WAIT', 'scheduler': 'owner_chat_wait',
            'automation_id': None, 'host_tool': None, 'host_kind': None,
            'prompt': (
                f'Wait ten minutes in this active chat, then observe once with {shlex.join(command)}. '
                'Post a short Chinese status even when unchanged. Follow the entry for faults and terminal cleanup.'
            ),
            'next_action': 'Verify the detached controller once, report its initial status, then wait 600 seconds in this owner turn.',
        })
    else:
        monitor.update({
            'registration': 'RECORDED_BY_OWNER', 'automation_id': heartbeat_id.strip(),
            'foreground': 'end_turn_after_handoff',
            'prompt': (
                f'Observe the existing run with {shlex.join(command)} once per wake. '
                'Post a short Chinese status in this chat on every wake, including unchanged progress. '
                f'Follow the fault and terminal instructions in {entry.with_name("README.md")}. '
                'End each foreground turn between wakes.'
            ),
            'next_action': 'Verify the detached controller once, post the initial status, then end this foreground turn.',
        })
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
            raise ValueError('A different heartbeat or owner monitoring mode is already recorded for this run')
    return monitor
