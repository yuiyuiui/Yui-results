"""Isolate the actual JSP-000175 T077 to T007 horizon interface with Lean."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys


def run(yui, contract_path, out):
    sys.path[:0] = [str(yui / 'nl02lean/scripts'), str(yui / 'nl0/scripts')]
    import dependency_instances
    import ir
    from native_workspace import temporary
    from runtime_config import scientific_pins

    contract = ir.contract(contract_path)
    header = contract['header']
    definition = re.search(r'(?ms)^def FiniteResampling : Prop :=\n(.*?)^def graphRank\b', header)
    if definition is None or definition[1].count('let T := heightL0 n') != 1:
        raise ValueError('Select the archived definition with the located fixed horizon')
    body = definition[1].replace('let T := heightL0 n', 'let T := horizon n')
    prefix = header.rstrip() + '\n\n' + dependency_instances.USE_PARSER + '''
namespace CubeRamsey
open scoped Classical
noncomputable section
def StudyLogSq (n : ℕ) : ℕ := ⌈(Real.log (n : ℝ)) ^ 2⌉₊
def StudyResamplingAt (horizon : ℕ → ℕ) : Prop :=
''' + body
    short = 'FiniteResampling'
    long = 'StudyResamplingAt StudyLogSq'
    old_type = 'StudyResamplingAt heightL0'
    checks = [
        ('independent_signatures', None, None, True),
        ('original_span_control', short, old_type, True),
        ('actual_consumer_cut', short, long, False),
        ('revised_internal_port_control', long, long, True),
    ]
    out.mkdir(parents=True, exist_ok=False)
    rows = []
    for name, producer, expected, should_pass in checks:
        source = prefix + '#check ' + short + '\n#check (' + long + ')\n'
        if expected is not None:
            ports = [{'id': 'T077', 'binder': 'h_T077',
                      'uses': [{'args': [], 'expected': expected}]}]
            source += dependency_instances.probes(contract, {'id': 'T007'}, ports,
                                                    f'(h_T077 : {producer})')
        source += '\nend\nend CubeRamsey\n'
        with temporary('yui-consumer-pilot-') as work:
            path = work / 'output/Check.lean'
            path.parent.mkdir()
            path.write_text(source)
            evidence = ir.run_lean(path, work, timeout=60)
        diagnostic = evidence['stdout'] + evidence['stderr']
        passed = ir.native_succeeded(evidence)
        uses = dependency_instances.failed_uses(source, diagnostic)
        expected_failure = (not passed and not evidence.get('timed_out') and uses
                            and 'type mismatch' in diagnostic.lower())
        observed = passed if should_pass else bool(expected_failure)
        ir.write(out / f'{name}.json', evidence)
        (out / f'{name}.lean').write_text(source)
        rows.append({'check': name, 'passed': passed, 'matched_oracle': observed,
                     'located_use': uses, 'wall_s': round(evidence['wall_seconds'], 3),
                     'generated_sha256': hashlib.sha256(source.encode()).hexdigest()})
    result = {'scope': 'Elaboration of one projected application. Neither internal proposition is proved here.',
              'contract_sha256': ir.digest(contract_path),
              'header_sha256': hashlib.sha256(header.encode()).hexdigest(),
              'pins': scientific_pins(), 'checks': rows}
    ir.write(out / 'measures.json', result)
    if not all(r['matched_oracle'] for r in rows):
        raise RuntimeError(f'Consumer-use regression. See {out}')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--yui', type=Path, required=True)
    parser.add_argument('--contract', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.yui.resolve(), args.contract.resolve(), args.out.resolve()),
                     indent=2))


if __name__ == '__main__':
    main()
