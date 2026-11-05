# Execute the unconditional Yui benchmark

This is the **single execution entry** for the Yui arm. A fresh local task needs
only: **“Execute this README.md.”** Follow the numbered stages below in order.
An explicit request to execute this entry authorizes one fresh run with the
checked-in settings, including its ordinary Yui repairs and owner monitoring.
Reading, editing or testing this entry does not start an experiment. Do not ask
for another start message, a pasted task prompt or already-configured choices.

Run all commands from **the directory containing this README**, wherever this
repository was cloned. `python3` must be the Python interpreter configured for
this installation. No `/Users/...` checkout path is required. Save the new run
path returned by stage 2; commands below use `RUN` for that exact path.

The creator opens the foreground task with **gpt-6.1-sol / high / Standard**.
For `create_thread`, set `model="gpt-6.1-sol"` and `thinking="high"` at
creation. Both the trusted [Yui-results project](../../.codex/config.toml) and
the paired Yui checkout select Standard. Send only
`Execute <path>/README.md`, using the absolute entry path when starting in Yui.

In the owning task, confirm your selected profile and the availability of a
permitted ten-minute heartbeat in this same chat. If either prerequisite fails,
report the reason in Chinese and end the turn before beginning the run.

## Formalization goal

This entry requests **unconditional formalization**: 2basis, shared NL0/Audit A and Lean/Audit B, then b2lean. The final check must validate `YuiClosed.P` and the actual b2lean receipt. Ordinary conditional Audit B is an intermediate result. Only an explicit user choice may retain class-4 assumptions; report the unmet unconditional goal and warnings.

## Scope, authority and configuration

- [settings.json](settings.json) selects the full Theorem 1 of the supplied
  original paper, `full` or `nl0`, `normal` repair, both model profiles, worker
  count, source hash, runtime pins and monitoring. This checkout is configured
  for `full` + `unconditional`, gpt-6.1-sol/high/Standard and 20 workers. `nl0` means NL0 plus
  Audit A only; do not start interfaces, Lean or Audit B for that setting.
- Read [AGENTS.md](AGENTS.md), then the exact registered `$rigorous-proof`
  `SKILL.md` returned by stage 1. Use its bundled operation, source qualification,
  repair and acceptance rules. This benchmark supplies the configuration and
  source-preparation procedure; Yui owns mathematical construction and review.
- A null runtime pin explicitly selects the single registered installation as
  it exists at preparation; its actual commit, branch, dirty state and complete
  runtime digest are recorded. For a fixed-version comparison, set
  `runtime.expected_commit` and/or `runtime.expected_sha256` in settings before
  starting. A mismatch blocks dispatch. Never substitute `main`, another checkout
  or another skill. Different prepared runtime/input digests qualify comparisons.
- Use no additional research/proof skill, agent-handoff protocol, peer task,
  standalone author/reviewer, sealed packet or alternative execution framework.
  The invoking task remains the owner; Yui manages its own isolated workers.
  PDF inspection uses the ordinary Poppler commands in stage 2, not another skill.
- Do not read `results/`, the pure-model arm, repository tests' mathematical
  outputs, earlier chats or old target/transcription files as construction
  material. Historic results are for separately requested **post-run analysis**.
  During construction, read/write only the current run and the declared entry,
  configuration, original paper and selected installation. Later literature
  retrieval follows Yui's own source rules; do not supply a previous source cache.
- The owner does not fill mathematical proof gaps, give workers hints, change
  frozen inputs or implement repairs. Yui's normal controller owns that work.
  Unsupported recovery, a public-contract defect or an actual user decision
  stays visible and waits for the user; it does not authorize a fresh attempt.

## File and directory responsibilities

Every current top-level item has one Yui-benchmark consumer:

| Item | Responsibility and stage |
| --- | --- |
| `README.md` | The sole operator procedure, stages 1–7 |
| `AGENTS.md` | Scope/authority rules for the invoking task, read before stage 1 |
| `settings.json` | Explicit run choices and input/runtime pins, stages 1–4 |
| `aim-518-kdv-log-loss.pdf` | The only initial mathematical source, stages 1–3 |
| `benchmark_config.py` | Strict settings and local-path validation, stages 1–4 |
| `skill_check.py` | Exact registered Yui discovery; no thread/model dispatch, stage 1 |
| `prepare_yui.py` | Source/run preparation and guarded calls to Yui, stages 1–7 |
| `owner_monitor.py` | Record the owning chat and host heartbeat before dispatch |
| `tests/` | Synthetic software tests for these stages; no proof fixtures or model calls, stage 1 |
| `results/` | Per-run inputs, bound runtime, proof/review evidence, monitoring and final reports, stages 2–7; old runs are read-only archives |

`tests/support.py` supplies synthetic registry, PDF-tool and Yui-runtime fixtures.
`test_config.py`, `test_discovery.py` and `test_pipeline.py` test configuration,
registry/environment handling and the prepare-to-close lifecycle respectively.
`test_runtime_contract.py` checks the real registered runtime's non-dispatch
prepare API with a neutral PDF when selected explicitly below.
Generated `__pycache__/` is disposable ignored Python cache, not an input.
There is no `.prepared/task.md` or second generated instruction authority.

## 1. Check software and the installed environment

Read this complete entry and the configuration before action. Confirm the
local prerequisites in [Yui's setup guide](https://github.com/yuiyuiui/Yui/blob/main/docs/setup.md).
The existing Yui isolation backend requires a compatible macOS environment;
cloning the repository does not make an unsupported operating system supported.
Install the complete Yui skill, not just SKILL.md. Put an authenticated compatible
Codex CLI on PATH or set `YUI_CODEX_BINARY`. Yui resolves its own pinned toolchain
and carrier settings. Source preparation requires Poppler's `pdfinfo` and `pdftoppm` on PATH (for example,
the `poppler` package). Text extraction uses `pdftotext` when available and
otherwise requires `pypdf` in the selected Python environment, as Yui already does.
No installation or toolchain upgrade is automatic.

```sh
python3 -B ../../entry_support/run_checks.py tests
python3 -B prepare_yui.py check
```

These calls start no model, proof, probe, benchmark or schedule. Environment
checking may read the authentication file's presence and run version queries;
it never prints credentials. The registry lookup uses only initialization and
`skills/list`. Missing, disabled, duplicate, malformed or incomplete registered
installations fail; a neighboring checkout is not a fallback. Model availability,
the 180-second native-call limit, unlimited total budgets, pinned tools and PDF
tools and the available PDF text backend are checked. Quota, future network health and the actual service tier stay
unverified.

Use the `installed.root` returned by `check` to run the neutral compatibility
check against that actual installation (substitute its resolved path):

```sh
YUI_TEST_INSTALLATION=/absolute/path/to/registered/Yui python3 -B -m unittest discover -s tests -p test_runtime_contract.py -v
```

It tests real PDF extraction/rendering, the begin/freeze/prepare adapter, and
`full`/`nl0` job preparation in temporary directories, then removes
them. It never executes the prepared jobs or reads the benchmark paper. The
ordinary synthetic suite skips this one environment-dependent test until the
actual installed path is known; do not report that skip as a tested runtime.

Read the returned installed skill entry and its operator/qualification rules.
Explain that inaccessible primary sources can lead to a conditional outcome,
which will retain its actual warnings. Do not read the paper or prepare its
mathematics before stage 2 starts the run's measurement.

## 2. Start measurement and prepare this run's complete paper

```sh
python3 -B prepare_yui.py begin
```

Save the returned `run` as `RUN`. The helper creates a fresh unique
`results/<run-id>/`, records the start **before its own environment check**, and
retains startup/configuration/runtime bindings in `BENCHMARK_RUN.json`. A failed
preflight prints a blocked result without starting a model. A failure after run
creation leaves that run and its failure record intact; do not replace it.

Inside `RUN/preparation/`, the helper:

1. Copies the original PDF as `original.pdf` and the exact operator files into
   `startup/` for provenance. No old run is opened.
2. Extracts the entire paper using Yui's existing `pdftotext -layout` backend,
   or its disclosed `pypdf` fallback, into `extracted.md`. The selected backend
   is recorded; raw extraction evidence must remain unchanged.
3. Renders **every PDF page**, including definitions, proof and bibliography,
   into `pages/`, at the configured DPI. The page count comes from `pdfinfo`.
4. Initializes `checked-source.md` from the extraction, an empty
   `target-statement.md`, and an unreviewed `source-review.json`.

The owner now actually inspects all rendered pages against the extracted text.
Correct lost hats, bars, signs, fractions, indices, exponents, coefficients,
quantifiers, ranges and displayed formulas in `checked-source.md`. Retain the
**complete paper in source order**, including all supplied proof steps. This is
source-only transcription: add no proof, derived lemma, external source,
interpretation replacing the original method, or old answer. The same full-paper
procedure applies to every run; there is no optional extra mathematical briefing.

Write `target-statement.md` from this run's original pages. Include the complete
Theorem 1 and every standing definition/hypothesis needed to interpret it:
objects and solution class; norm/measure/Fourier conventions; exact update maps
and normalization; all parameters, endpoints and quantifier order; dependence
and uniformity of constants; and the full time grid and conclusion. Check the
surrounding definitions and proof, not just the theorem's page. Referenced
transformations, exact evolution equations and operator definitions remain
available in the complete checked source. Preserve the supplied proof route.
Do not silently strengthen or weaken the theorem to simplify formalization.

Complete `source-review.json` truthfully:

- Keep its schema and original source hash.
- List every actually checked page exactly once in `checked_pages`.
- Set `transcription_checked`, `target_checked` and `source_only` to true only
  after completing those checks.
- For each transcription correction record `{ "page": N, "detail": "..." }`;
  use an empty list only if no correction was needed. Retain concrete notes
  about unresolved extraction problems. If fidelity cannot be established,
  stop and report the blocked preparation; do not attest that it passed.

Software can check complete fields, page coverage and byte bindings; the
readback record is **an owner attestation**, not machine verification of the
transcription's mathematics. Independent Audit A still checks source fidelity.
Do not call another model or another skill to prepare a mathematical briefing.
The invoking task's work here is part of measured preparation; its unexposed
provider usage is unknown, not zero.

## 3. Freeze reviewed inputs and prepare the configured Yui job

```sh
python3 -B prepare_yui.py freeze RUN
python3 -B prepare_yui.py prepare RUN
```

Replace `RUN` with this run's returned absolute path, using normal shell quoting
for paths with spaces. `freeze` accepts only the current run's complete review,
checks the original/exported bytes and asks the registered Yui target resolver
to bind `target-statement.md` to this run's `original.pdf`. It creates
`preparation/target-selection.json` and freezes all reviewed input hashes.

`prepare` calls Yui's existing `prepare` entry with exactly:

- This run's original PDF as the problem.
- The explicit `formalization` goal from this directory's settings.
- This run's complete `checked-source.md` as its sole extra material.
- This run's source-bound target selection.
- The configured track, normal policy, phase profiles and worker count.
- A fresh output at `RUN/workflow/`.

Neither command starts a model or Lean proof. Job preparation is checked for
unexpected documents, imported authority, target drift, profile/worker changes
and output escape. Source, entry, configuration, tools or installed-runtime
changes make preparation stale and block launch. Do not repair that by rewriting
old bindings. A failed submitted preparation remains a failed attempt; report it
instead of automatically making a replacement run.

## 4. Register the heartbeat and dispatch once

After preparation, register **one active host heartbeat every 10 minutes
(600 seconds) in this same chat** with `automation_update`. Reuse a matching
heartbeat for this chat and run, updating its cadence, wake instruction and
notification settings if necessary. Include this README's absolute path and
the exact `RUN/workflow` path. Substitute the absolute script and run paths
in the wake instruction below.

> Run `python3 -B prepare_yui.py observe RUN` once. Post a short status in Chinese with
> the phase, available completion counts and any fault or decision. **Report
> even when progress is unchanged.** For a running or paused case, end this
> turn after posting. At termination, follow the README to validate, report,
> clean up and remove the heartbeat.

Use the host-returned heartbeat ID as `HEARTBEAT_ID`. If registration fails,
report the prepared run and the error, leave the workers undispatched and end
the turn. Do not switch to foreground sleeping or polling.

```sh
python3 -B prepare_yui.py launch RUN --heartbeat-id "$HEARTBEAT_ID"
python3 -B prepare_yui.py observe RUN
```

`launch` saves the ID, owning chat and workflow map in
`RUN/OWNER_MONITOR_STATE.json` before dispatching once with `--detach`. Verify
the controller PID, start time and process group in the initial observation.
Post the initial status and **end the foreground turn**. The background workers
continue until the next heartbeat wakes this chat.

If dispatch is ambiguous, observe the existing workflow once and report what
is known. Keep its heartbeat for live or unconfirmed work. If dispatch failed
and no owned work started, delete the idle heartbeat by its host-returned ID
and end the turn. Never repeat an ambiguous launch.

## 5. Observe and handle actual faults within Yui's boundaries

On each wake run only the bounded observation above. Read bounded new fault
metadata when needed. Do not inspect unfinished proofs to guide workers, send
hints, read another run, repeat foreground waits, restart live work or resample
mathematical failures.

`PAUSED_ERROR` is nonterminal. Keep its monitor and evidence. Report the actual
incident and the supported Yui operation/user decision required. Normal local
repairs are already delegated to Yui. No independent recovery workflow or
runtime editing is authorized by this entry. Preserve all failures, retries,
continuation costs and source warnings; elapsed time alone is not model failure.

If the user cancels this run, use:

```sh
python3 -B prepare_yui.py cancel RUN
```

Before a Yui job exists this records `CANCELLED_PREPARATION` and stops source
work, with no Yui model dispatch. Preserve that preparation outcome and report
its owner time/unknown usage; the native terminal `finish` step does not apply.

Cancellation is a request, not proof of process exit. Continue bounded ownership
checks until the actual owned processes/groups exit. Do not kill unrelated
processes or discard results. Cleanup applies only to the selected run and only
within the installed Yui cleanup rules and actual user authorization.

## 6. Validate existing terminal evidence and close the run

Once the actual result is terminal, no paused incident is pending and all exact
owned processes/groups have exited:

```sh
python3 -B prepare_yui.py finish RUN
```

`finish` refuses a live/paused run, unknown process exit or duplicate final
outcome. It validates the actual job binding, existing NL0/Audit A authority and,
when present, the bound final machine Audit B receipt with this run's frozen
validators. It starts **no model, Lean build or probe**. It writes
`RUN/FINAL_OUTCOME.json` with actual status, validation, source warnings, health,
recorded usage, preparation wall time, case wall time and total wall time to the
terminal record. Observer/closure delay is recorded separately, not added to the
case duration. The total includes the input-preparation work previously omitted
from some historical case-only timings.

Inspect the linked, actual gate reports after termination. Keep these outcomes
separate in `RUN/FINAL_REPORT.zh.md`:

1. Mathematical acceptance: source-faithful NL0/Audit A; for `full`, independently
   reviewed frozen interfaces, assembly, kernel trust and machine Audit B.
   Compilation or a saved PASS by itself is not a source-fidelity proof.
2. Conditional sources and all actual warnings, including exceptional B-final
   qualifications. Do not upgrade conditional evidence to an ordinary PASS.
3. Execution health: actual transport, controller, tool or cleanup faults,
   external cancellation and any explicitly authorized continuation.
4. Accounting: preparation versus case/stage/total time, observed usage and
   missing coverage. Cached input/reasoning output are already subsets; do not
   add them again. Missing operator/provider usage and actual tier stay unknown.

Record N/R counts, S/F organization, local R review work/repair distribution,
phase times and, for full runs, Lean T times and their long tail from terminal
metadata. If a reporting utility fails, retain its diagnostic and label any
fallback derived from existing records; do not launch another experiment.

After preserving the machine and Chinese human reports, complete stage 8.
Retain the heartbeat while an authorized recovery is pending.

## 7. Result layout and historical records

```text
results/<new-run-id>/
  BENCHMARK_RUN.json          Owner state, exact configuration and bindings
  preparation/
    startup/                 This run's entry/configuration/helper snapshot
    original.pdf             Byte-identical initial source
    extracted.md             Unchanged full raw extraction
    pages/                   Complete rendered source pages
    checked-source.md        Full source-only mathematical transcription
    target-statement.md      Complete source-selected statement/definitions
    source-review.json       Actual page/correction/readback attestation
    target-selection.json    This run's Yui-bound target
  prepare-attempt.json       One job preparation attempt and result/error logs
  prepare-result.json
  workflow/                  Actual Yui job, inputs, runtime, proofs and reviews
  dispatch-attempt.json      One dispatch attempt and result/error logs
  dispatch-result.json
  OWNER_MONITOR_STATE.json   Actual host schedule ID and this workflow map
  OWNER_MONITOR_LOG.jsonl    Bounded owner observations
  FINAL_OUTCOME.json         Bound terminal validation, health and accounting
  FINAL_REPORT.zh.md         Chinese final report
```

These records are evidence, not extra instruction packets. Every new run starts
with its own empty preparation. An incomplete/failed run retains its actual
record and files; not every listed terminal artifact will exist.

This directory is the unconditional benchmark. Historical conditional runs
remain under `../../benchmark_cond/Yui/results/`; they are never construction inputs.

Regression coverage includes `test_modes_cleanup.py`: explicit goals, final b2lean acceptance, cancellation and resource-only cleanup.

## 8. Clean up owned resources before ending

`resource_cleanup.py` is the snapshotted resource-only cleanup helper used below.

```sh
python3 -B prepare_yui.py cleanup RUN
```

Executing this README authorizes cleanup after the actual run terminates. Stop
only verified owned residual background helpers; confirm process/group exit;
remove marked native scratch, disposable hidden caches, unneeded compilation
and atomic temporary files. If finalization is blocked only by residual helpers
after a genuine terminal case-result.json, cleanup may run first, followed by
finish and a final cleanup check. Never clean active/paused work.

Preserve the original/source readback, Lean sources/final proofs, A/B/b2lean
receipts, compiler/diagnostic logs, bound evidence and reproducibility runtime.
Preserve compiled artifacts referenced by evidence, shared Lean/mathlib, other
runs and symlink targets. The helper writes CLEANUP.json. Unknown ownership or
unconfirmed exit must leave diagnostics and report CLEANUP_BLOCKED, not claim
a clean disk/memory state. The final Chinese report must state cleanup status.
Once the run is terminal, owned processes have exited, and final reporting and
cleanup are complete, delete its heartbeat by its saved ID and record the
deletion in `RUN/OWNER_MONITOR_STATE.json`. Post the final Chinese status and
end the turn.
