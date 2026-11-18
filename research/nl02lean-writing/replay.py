"""Measure proof tool payloads on unchanged archived candidate trajectories."""

import argparse
import hashlib
import json
from pathlib import Path
import sys


def wire_bytes(args):
    return len(json.dumps(args, ensure_ascii=False, separators=(',', ':')).encode())


def edit_candidate(base, old, new):
    if old == new:
        return {'edit': {'base': base}}
    before, after = old.splitlines(keepends=True), new.splitlines(keepends=True)
    first = 0
    for left, right in zip(before, after):
        if left != right:
            break
        first += 1
    tail = 0
    for left, right in zip(reversed(before[first:]), reversed(after[first:])):
        if left != right:
            break
        tail += 1
    # Keeping one context line provides an anchor for a pure insertion.
    if first:
        first -= 1
    elif tail:
        tail -= 1
    anchor = ''.join(before[first:len(before) - tail])
    replacement = ''.join(after[first:len(after) - tail])
    if anchor.strip():
        return {'edit': {'base': base, 'old': anchor, 'new': replacement}}
    return None


def replay(root, expand):
    rows = []
    for folder in sorted(root.rglob('lean-drafts')):
        previous = {}
        last = None
        for path in sorted(folder.glob('proof-*.json')):
            value = json.loads(path.read_text())
            body, result = value.get('proof'), value.get('check')
            if not isinstance(body, str) or not body.strip() or not isinstance(result, dict):
                continue
            if type(result.get('exit_code')) is not int:
                continue
            number = int(path.stem.split('-')[1])
            full = {'proof': body}
            proposed = edit_candidate(last, previous[last]['proof'], body) if last is not None else None
            if proposed is not None:
                try:
                    decoded = expand(proposed, previous)
                except ValueError:
                    proposed = None
                else:
                    if decoded != body:
                        raise AssertionError(f'Candidate reconstruction changed: {path}')
            use_edit = proposed is not None and wire_bytes(proposed) < wire_bytes(full)
            rows.append({'draft': str(path.relative_to(root)),
                         'body_sha256': hashlib.sha256(body.encode()).hexdigest(),
                         'check_exit': result['exit_code'],
                         'same_as_previous': last is not None and body == previous[last]['proof'],
                         'edit': use_edit, 'full_bytes': wire_bytes(full),
                         'selected_bytes': wire_bytes(proposed if use_edit else full)})
            previous[number] = {'proof': body}
            last = number
    if not rows:
        raise ValueError(f'No checked draft records found under {root}')
    return rows


def summary(rows):
    return {'candidates': len(rows), 'edit_used': sum(x['edit'] for x in rows),
            'same_as_previous': sum(x['same_as_previous'] for x in rows),
            'full_bytes': sum(x['full_bytes'] for x in rows),
            'selected_bytes': sum(x['selected_bytes'] for x in rows)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--yui', type=Path, required=True)
    parser.add_argument('archive', type=Path, nargs='+')
    args = parser.parse_args()
    sys.path[:0] = [str(args.yui / 'nl02lean/scripts'), str(args.yui / 'nl0/scripts')]
    from proof_edits import expand

    results = []
    for archive in args.archive:
        rows = replay(archive, expand)
        results.append({'archive': str(archive), 'all': summary(rows),
                        'changed_bodies': summary([x for x in rows if not x['same_as_previous']]),
                        'rows': rows})
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
