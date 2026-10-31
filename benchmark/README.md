# Independent Yui benchmark

This directory contains everything its invoking task needs: the original PDF,
portable settings, installed-skill discovery, preparation code and operator
instructions. It imports nothing from another benchmark directory. Its exact
benchmark/skill identity is in [settings.json](settings.json); read
[operator instructions](AGENTS.md) before dispatch.

The target is the paper's **complete Theorem 1**, including its actual method,
standing definitions, hypotheses, quantifiers, parameter ranges and conclusion.
The owner checks extracted notation and freezes the target from this original,
without importing an old proof or adding a different method. The PDF is the only
initial mathematical input. Sources obtained later use the selected skill's
ordinary retrieval and source-correspondence rules.

## Fixed setup

| Setting | Selected value |
| --- | --- |
| Skill | Exact enabled installed `skill_name` in settings.json |
| Track/policy | Full / normal, with located repair |
| NL0 and Audit A profile | gpt-6.1-sol / high / Standard; no fallback |
| Lean preparation/proof/assembly/Audit B profile | gpt-6.1-sol / high / Standard; no fallback |
| Per-case workers | 20, retained from the selected benchmark configuration |
| Parallel phases | Local R reviews, then local Lean proofs in a separate phase |
| Serial lanes | NL0 author, global A, preparation/interfaces, assembly and B |
| Whole-case/stage time, tokens, model calls | Unlimited |
| One native Lean call | 300 seconds; normal diagnosed repair follows |
| Owner observation | Detached; one bounded host heartbeat every 600 seconds |
| Previous answers/proofs/source caches | No reuse |

The two versions use the same startup program, operator contract, PDF and
settings except their benchmark/skill identity. The selected skill's internal
workflow is the experiment variable. Model nondeterminism, account quotas,
external website availability and shared-host contention remain observable
qualifications rather than controlled guarantees.

## Prepare without starting

Run these commands **from this directory**, not another benchmark:

```sh
python3 -B skill_check.py
python3 -B prepare_yui.py --workers 20 --write-preparation
python3 -B prepare_yui.py --verify-preparation
python3 -B -m unittest discover -s tests -v
```

Discovery calls only Codex initialization and `skills/list`. Preparation checks
the installed skill and runtime binding, local model/effort metadata, credential
file presence, sandbox availability, pinned Lean/Mathlib/dependency versions,
the native limit and PDF text extraction. It calls no model, theorem probe or
Lean build; the Lean executable is used only for its version. Extraction needs
`pdftotext -layout` or the installed skill's Python `pypdf` fallback. Successful
extraction is readability, not a mathematical-fidelity verdict.

The generated `.prepared/readiness.json` and `.prepared/task.md` contain actual
resolved paths, hashes, prerequisites and the future-task instruction. They are
local ignored files: regenerate them after cloning or relocation. Verification
rejects changed inputs, settings, operator instructions, runtime or tool pins.
No job, proof queue, result directory, model session or schedule is created.
`READY_AWAITING_USER_START` means preparation only. Provider quota/network health
and the future observed service tier cannot be guaranteed by these checks.

Tool locations are resolved by the installed skill. Supported overrides include
`YUI_CODEX_BINARY`, `YUI_LEAN_ROOT` and `YUI_MATHLIB_ROOT`; never embed one user's
checkout path into portable source. Another local repository is not an installed
skill, and a missing variant never falls back to a different one.

## Start after human authorization

The coordinating owner creates a **fresh Codex task** only after the human says
to start. Before creating the two tasks, that owner rechecks equal PDF hashes
and equal normalized portable settings. It sends each directory's generated
`.prepared/task.md`, with explicit
start authorization. That task reads this directory and the exact selected
installed skill, rechecks prerequisites, freezes the original target, then
dispatches the full workflow with a fresh explicit output directory.

The task verifies detached process identities, registers a real ten-minute host
heartbeat and ends its foreground turn. Every check is bounded and ends as well.
No foreground polling is required. Missing scheduling must be disclosed.

## Results and accounting

```text
results/
  <unique-run-id>/
    inputs/                  Original/extracted paper and complete target
    runtime/                 Bound code and rule snapshot
    ...                      Actual skill-owned proof, review and native files
    OWNER_MONITOR_STATE.json Actual schedule ID and current run map
    OWNER_MONITOR_LOG.jsonl   Bounded owner observations
    FINAL_OUTCOME.json       Actual terminal status, qualifications and costs
```

The installed runtime owns its actual internal filenames. Keep job, launch,
configuration, worker, source, warning, proof, audit, compilation and execution
evidence together under the run. Copy the preparation and task instruction into
owner provenance, outside measured mathematical inputs. Never overwrite an old
run or store results in the installed skill. Preserve earlier stopped attempts
and include every authorized continuation's time and known tokens.

Keep complete Audit A, conditional local checks, standalone assembly, native
trust inspection and independent semantic Audit B separate. Every external
theorem and the full target, including hypotheses, need actual correspondence.
Inaccessible originals require visible warn.json/warn.md and conditional status;
a compiler pass or author self-report is not independent semantic acceptance.

Measure actual dispatch-to-terminal wall time, phase wall time, source/tool/native
time when recorded, retries/repairs and token completeness. Deduplicate response
IDs; cached input and reasoning output are subsets. Missing usage stays unknown.
Separate mathematical acceptance, execution health and measurement validity.
Requested Standard is not proof of an observed tier when the provider omits it.

The coordinating owner compares selected **terminal** runs after both groups
exit. It must not feed findings back into either construction or read another
arm's unfinished proof. Equal settings do not make concurrent wall times an
isolated speed experiment, and an unfinished arm cannot establish speedup.
