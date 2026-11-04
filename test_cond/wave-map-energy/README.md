# Execute this conditional test: Wave-map energy conservation

This README is the single execution entry for **this one problem**. In a fresh
Codex task, “Execute test_cond/wave-map-energy/README.md” authorizes one fresh complete
run using [settings.json](settings.json), ordinary Yui repair, observation,
terminal reporting and safe resource cleanup. Do not ask for a second start
message or run another problem. Reading/editing this entry or its software tests
does not authorize an experiment.

Use the directory containing this README as the command working directory.
No machine-specific absolute path is required. Keep the `run` path returned by
`begin` as `RUN`; it always identifies this exact current run.

## Scope and fixed configuration

- Source: [problem.md](problem.md), including its complete proof and approved
  interpretations. The target comes from its configured complete-target section,
  read fresh from this run's copy. Use no old target-selection JSON.
- Goal: **conditional**, `full`, normal repair; NL0 → Audit A → frozen Lean interface → local Lean proofs/assembly → Audit B.
- Both phase profiles: **gpt-6.1-sol / high / Standard**, no fallback;
  **10 local workers**, unlimited total budget, 180-second native-call limit.
- Use only the exact registered `$rigorous-proof` installation and its bundled
  operation/rules. Read its SKILL.md after discovery. Do not substitute a sibling
  checkout, another skill, a peer task or an owner-written proof.
- Preserve the supplied proof route and complete original hypotheses. Literature E statements may remain explicit premises; report them.
- Old `rigorous-proof/` runs and `target-selection*.json` are historical evidence,
  never construction input. Conditional/unconditional siblings do not exchange
  proofs, target files, source caches or review judgments.

## 1. Check the entry and installed runtime

```sh
python3 -B ../../entry_support/run_checks.py ../../entry_support/tests
python3 -B run_test.py check
```

These commands start no model, theorem probe, Lean proof or schedule. `check`
verifies source hash, target section, exact registry selection, profiles and
runtime capability. Read the returned installed SKILL.md and relevant rules.
The unconditional entry must reject an installation lacking 2basis/b2lean.
Resolve a missing installation/configuration before starting; never improvise
another execution framework. Apply host-level tool and monitoring policies.

## 2. Begin measurement and actually read the current source

```sh
python3 -B run_test.py begin
```

Save the returned `run` path. The helper starts measurement, creates a unique
`rigorous-proof/<run-id>/`, snapshots the entry/shared adapter, copies this
problem, and extracts its complete configured target section. It does not call
an author. A failed preparation stays recorded; do not erase it or silently
start another run.

Read **all** of `RUN/preparation/problem.md` and
`RUN/preparation/target-statement.md`. Check every standing assumption,
normalization, parameter range, endpoint and conclusion against the configured
source section. Keep the supplied mathematics and approved interpretations.
Do not repair the proof or add hints. The existing source is UTF-8 Markdown;
there is no PDF transcription or another model preparation stage.

After that actual readback, edit only `RUN/preparation/source-review.json`:
retain schema/source hash; set `source_read`, `target_checked`, `source_only`
to true; write a truthful short `notes`. Do not attest to unread work.
This is an owner readback record, not independent mathematical acceptance.

## 3. Prepare and dispatch exactly once

```sh
python3 -B run_test.py prepare RUN
python3 -B run_test.py launch RUN
python3 -B run_test.py observe RUN
```

`prepare` makes a fresh source-bound target selection and calls Yui prepare with
this copied problem, explicit goal/profiles/workers and a new `RUN/workflow`.
It rejects stale/extra inputs or changed goal/target. `launch` uses that job's
frozen runtime and rejects a repeated dispatch, including an ambiguous failure.
No old proof or result is supplied. Only `launch` starts model work.

`DISPATCHED` means pending work, not completion. Verify the returned PID/start
identity/PGID and exact run map through the bounded observation. Keep this same
owning task responsible until termination. Follow the installed owner-observation
policy subject to host policies: use an allowed host heartbeat only when the
host permits it and record its actual ID; otherwise keep bounded in-task checks.
Do not invent a schedule, add another scheduler, send worker hints or claim an
unregistered monitor. Report in Chinese only for meaningful progress, faults,
required user choices or completion. Do not leave an unobserved run.

## 4. Handle real findings and explicit user decisions

Ordinary local repair belongs to Yui. Preserve actual source qualifications,
transport faults, cancellation and incomplete usage separately. Do not edit
bound inputs, entry configuration or runtime to get a live run past a failure.
Use only the installed runtime's supported exact-incident controls. In
unconditional mode, show the actual class-4 stop/continue/accept-conditional
choices and wait for the user's selection. Do not accept residual assumptions
on the user's behalf. A retained PAUSED_ERROR is not terminal.

An explicit user cancellation uses:

```sh
python3 -B run_test.py cancel RUN
```

A cancellation request is not proof of exit. Continue bounded ownership checks.
A preparation cancelled before any job/dispatch is `CANCELLED_PREPARATION`;
retain its source/diagnostic and report that no mathematical run occurred.

## 5. Validate and report the actual terminal result

After the real case terminates and no paused incident remains:

```sh
python3 -B run_test.py finish RUN
```

The helper verifies current job binding, existing Audit A and Audit B, and the
actual final b2lean proof for an unconditional delivery. It performs no new
mathematical review or Lean build. It writes `FINAL_OUTCOME.json` and
`FINAL_REPORT.zh.md`. Read both and report the requested versus achieved scope,
actual assumptions/warnings, process exit, wall time and observed token coverage.
Do not claim a complete unconditional result from a conditional receipt.
Missing usage is unknown; cached/reasoning tokens are subsets, not additions.

## 6. Clean up before ending this task

```sh
python3 -B run_test.py cleanup RUN
```

This cleanup is authorized by executing this README, after actual termination.
It stops only precisely owned residual helpers, confirms their exit, removes
marked native temporary workspaces and unneeded cache/compilation/atomic scratch
files (including disposable hidden caches), and writes `CLEANUP.json`.
If `finish` is blocked only by residual helpers after a genuine terminal
`case-result.json`, `cleanup` may run first, then repeat `finish` and `cleanup`.
It must refuse active/paused work or unconfirmed ownership.

**Preserve** original inputs, Lean sources and final proofs, A/B/b2lean receipts,
compiler/diagnostic logs, bound evidence and frozen reproducibility runtime.
Never purge shared Lean/mathlib, symlink targets, sibling runs, or unknown
processes. Compilation files still referenced by an evidence record are useful
artifacts and are retained. If cleanup is blocked, retain diagnostics and report
what remains; do not claim disk/memory cleanup succeeded. Remove an allowed
monitor only after its actual run has ended, using its recorded ID. Final reply
must state cleanup status and retained result location, then end the task.
