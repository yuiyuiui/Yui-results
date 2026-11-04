# Reproducing the pure-model benchmark

Start from [README.md](README.md). There are three distinct operations below:
a new from-scratch evaluation, a reproduction of the historical supplementary
repair, and a compiler rebuild of the accepted sources. Only the first is a
new independent attempt at the whole paper.

## Environment and fixed inputs

- Use the original [paper](aim-518-kdv-log-loss.pdf), SHA-256
  `5d6432bf9c097991bf5d853f38e831a539b4f052f0ccf4010bba6e37b54507b6`.
- Use Lean **4.32.2** and Mathlib commit
  `905b95818eb32af7874a58b427f50c1711a5e96c`, with its pinned dependencies and
  compiled cache. Follow the repository's [local setup](../../README.md#local-setup).
  Reuse the shared installation; do not run `lake update` or change it.
- For model work, use an authenticated native Codex CLI and request
  **gpt-6.1-sol / high / Standard**, with no automatic model fallback and no
  total time, token, model-call or iteration limit. Save the actual resolved
  tool paths, model configuration and code version with the new run. Do not
  infer the provider's actual tier from the requested value.
- Give the mathematical author no Yui proof instructions, personal skills,
  memories, other agents' solutions or previous benchmark verdicts. Evaluation
  is separate from construction. Use ordinary native tools, without adding a
  new proof workflow or a custom operating-system sandbox.
- Create a fresh `pure-model-result/<new-run-id>/` for each experiment. Retain
  the exact inputs, rendered prompt, native session ID, event streams, errors,
  timestamps, candidate files, reviews and final outcome there. Never overwrite
  either archived run.

Reading or rendering a task does not launch a model. Start model work only when
the user has requested the corresponding experiment.

## 1. New from-scratch evaluation

Open a fresh local Codex task at the repository root and give it this instruction:

```text
Run a new from-scratch pure-model benchmark now. Start at
benchmark_cond/pure-model-result/README.md and follow section 1 of REPRODUCE.md.
Use only benchmark_cond/pure-model-result/aim-518-kdv-log-loss.pdf and its cited sources as mathematical
inputs, with the pinned Lean/Mathlib. Render the author task from prompt.py.
Use one clean native author session, gpt-6.1-sol/high/Standard, without Yui proof
rules, personal skills/memories, other agents or previous benchmark results.
Save everything in a fresh benchmark_cond/pure-model-result/<new-run-id>/.
Have a separate context evaluate the complete target and source correspondence.
Return necessary repair feedback to the same author session and record those
costs separately. Report the final outcome, execution faults, elapsed time and
observed/unknown usage. Do not treat compilation alone as semantic acceptance.
```

The owner renders [prompt.py](prompt.py) with this machine's absolute paths by
calling `render(paper=..., lean=..., mathlib=...)`; save its exact returned text
as the new run's `prompt.md`. The author receives that task, a byte-identical
copy of the paper and access to the cited primary sources and pinned libraries.
The original author's outputs, the supplement and their reviews are excluded
from a fresh run's mathematical inputs.

Require `Proof.lean`, `correspondence.md`, `result.json` and any source warnings.
The target is the full Theorem 1, including its exact unfiltered scheme,
definitions, hypotheses, quantifiers and conclusion. Independently check the
complete exported signature and external-source correspondence, not only its
successful compilation. Keep repairs in the same mathematical author session;
a normal turn ending is not a new independent attempt.

`runner.py` is retained for reproducing the original direct-supervisor launch.
It resolves the installed Yui **transport/supervisor code**, while the measured
author receives only the bare-model prompt, not Yui's proof workflow. Its
mechanical completion check reports `CANDIDATE_READY`; independent semantic
acceptance remains a separate step. To use that historical launch path, run
the following from this directory after selecting actual absolute paths:

```sh
python3 -B runner.py --work /absolute/path/to/new-run \
  --paper /absolute/path/to/benchmark_cond/pure-model-result/aim-518-kdv-log-loss.pdf \
  --lean /absolute/path/to/lean --mathlib /absolute/path/to/mathlib \
  --codex /absolute/path/to/codex --prepare-only
```

This only prepares the prompt. Removing `--prepare-only` starts paid model work
and may continue the same author session until mechanical completion. Record
the installed supervisor version if using it; it is not used for section 2's
supplement protocol.

## 2. Reproduce the historical supplementary repair

This operation deliberately takes the historical author's own candidate as
input. It measures repair of that candidate, not a fresh solution of the paper.

1. Read [supplement-preparation/README.md](supplement-preparation/README.md),
   [settings.json](supplement-preparation/settings.json) and
   [prompt.md](supplement-preparation/prompt.md).
2. Resolve every configured input relative to this `pure-model-result/`
   directory and verify its recorded SHA-256 before staging. The allowed inputs
   are the target paper, the two primary literature PDFs, the original
   `Proof.lean`, and that author's own correspondence/warnings. The historical
   execution record is for accounting, not mathematical guidance. Do not copy
   neighboring post-hoc audit reports with the primary PDFs.
3. Create a new run directory with a separate `work/` directory. Copy the
   original proof unchanged as `work/OriginalProof.lean`. Render all placeholders
   in the supplement prompt with the staged input, work and tool paths. Save
   the rendered prompt and input bindings with the new run.
4. Start one fresh native author session using the settings above. Use the
   ordinary native environment and passive time/usage recording. Do not use
   `runner.py`, an automatic verifier-feedback controller or an additional
   proof skill. The retained [author process record](20261101T114606Z-5d3193f6/owner-records/author-001-process.json)
   and [native configuration](20261101T114606Z-5d3193f6/native-home/config.toml)
   document the historical invocation; their old absolute paths must be
   resolved for the new run, not executed verbatim.
5. Require exact original external statements, proved bridges where needed,
   the unchanged original proof, completed target, source/bridge ledger and
   full build/signature evidence. Obtain a separate-context semantic review of
   the actual candidate. Keep any explicitly authorized feedback and continued
   author turns in the same run and record every turn; the template itself
   implements no automatic continuation policy.
6. Report the new supplement's costs separately from the historical original
   costs and from evaluator costs before presenting any combined total. Preserve
   failed candidates and transport faults. An unavailable usage counter remains
   unknown; cached and reasoning counters are not added twice.

The retained supplement used two author turns and three evaluator turns. Its
[original rendered prompt](20261101T114606Z-5d3193f6/owner-records/author-prompt-001.md),
[continuation prompt](20261101T114606Z-5d3193f6/owner-records/author-prompt-002.md)
and [stage usage](20261101T114606Z-5d3193f6/owner-records/native-stage-usage.json)
document what actually happened. New runs need not take the same number of
turns or produce the same timing or proof.

## 3. Rebuild the accepted proof without model work

The following rebuilds the eleven delivered modules from the accepted snapshot
in a temporary directory, using the current machine's pinned tools. It leaves
the archive and its historical logs untouched. Run it from this directory,
replacing the two example paths with the actual installations:

```sh
python3 -B - /absolute/path/to/lean /absolute/path/to/mathlib <<'PY'
from pathlib import Path
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile

lean = Path(sys.argv[1]).expanduser().resolve(strict=True)
mathlib = Path(sys.argv[2]).expanduser().resolve(strict=True)
version = subprocess.check_output([str(lean), '--version'], text=True)
if not version.startswith('Lean (version 4.32.2,'):
    raise SystemExit('Expected Lean 4.32.2: ' + version)
commit = subprocess.check_output(
    ['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
if commit != '905b95818eb32af7874a58b427f50c1711a5e96c':
    raise SystemExit('Mathlib commit mismatch: ' + commit)

source = Path('20261101T114606Z-5d3193f6/frozen-candidate-002').resolve()
expected = 'bf73ff25c1c67c020023ad545649bd2e0444658191c6c0c637b86528ad0b0cd0'
if hashlib.sha256((source / 'OriginalProof.lean').read_bytes()).hexdigest() != expected:
    raise SystemExit('Historical proof hash mismatch')
work = Path(tempfile.mkdtemp(prefix='pure-model-rebuild-'))
for path in source.glob('*.lean'):
    shutil.copyfile(path, work / path.name)
libraries = [work, mathlib / '.lake/build/lib/lean']
libraries += sorted((mathlib / '.lake/packages').glob('*/.lake/build/lib/lean'))
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libraries)))
modules = [
    'OriginalProof', 'OriginalExternals', 'GalerkinBridges', 'ExternalBridges',
    'StageBridges', 'PaddingHelpers', 'FlowLimitHelpers', 'RegularityBridges',
    'SolutionCorrespondence', 'CompletedProof', 'SignatureInspection',
]
print('Build output:', work, flush=True)
for name in modules:
    with (work / (name + '-build.log')).open('w') as log:
        subprocess.run([str(lean), '-o', name + '.olean', name + '.lean'],
                       cwd=work, env=env, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    print(name + ': built', flush=True)
print('Signature and axiom output:', work / 'SignatureInspection-build.log')
PY
```

A successful rebuild checks compilation of the retained sources. It does not
repeat the independent mathematical/source review, reproduce model behavior or
reproduce timing/token measurements. The recorded semantic evidence remains
the [acceptance report](20261101T114606Z-5d3193f6/review-003-output/acceptance-report.md)
and [scope concordance](20261101T114606Z-5d3193f6/review-003-output/scope-concordance-report.md).
