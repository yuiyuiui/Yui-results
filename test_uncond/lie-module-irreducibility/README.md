# Execute this unconditional test: Reduction of an admissible sl2 lattice

This README is the single execution entry for **this one problem**. In a fresh
Codex task, “Execute test_uncond/lie-module-irreducibility/README.md” authorizes one fresh complete
run using [settings.json](settings.json), ordinary Yui repair, observation,
terminal reporting and safe resource cleanup. Do not ask for a second start
message or run another problem. Reading/editing this entry or its software tests
does not authorize an experiment.

Use the directory containing this README as the command working directory.
No machine-specific absolute path is required. Keep the `run` path returned by
`begin` as `RUN`; it always identifies this exact current run.

The creator opens the foreground task with **gpt-6.1-sol / high / Standard**.
For `create_thread`, set `model="gpt-6.1-sol"` and `thinking="high"` at
creation. Both the trusted [Yui-results project](../../.codex/config.toml) and
the paired Yui checkout select Standard. Send only
`Execute <path>/README.md`, using the absolute entry path when starting in Yui.

In the owning task, confirm your selected profile and the availability of a
permitted ten-minute heartbeat in this same chat. If either prerequisite fails,
report the reason in Chinese and end the turn before beginning the run.

## Scope and fixed configuration

- Source: [problem.md](problem.md), including its complete proof and approved
  interpretations. The target comes from its configured complete-target section,
  read fresh from this run's copy. Use no old target-selection JSON.
- Goal: **unconditional**, `full`, normal repair; 2basis → the same NL0/Audit A and Lean/Audit B → b2lean final closure.
- Both phase profiles: **gpt-6.1-sol / high / Standard**, no fallback;
  **10 local workers**, unlimited total budget, 180-second native-call limit.
- Use only the exact registered `$rigorous-proof` installation and its bundled
  operation/rules. Read its SKILL.md after discovery. Do not substitute a sibling
  checkout, another skill, a peer task or an owner-written proof.
- Only Yui 2basis may change the proof route. Preserve the original target/H, quantifiers, parameter ranges and constant dependencies. Verify the final YuiClosed.P and b2lean receipt; intermediate Audit B is insufficient. Remaining class-4 dependencies require the actual user choice; never silently downgrade this goal.
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

## 3. Prepare, register the heartbeat and dispatch once

```sh
python3 -B run_test.py prepare RUN
```

`prepare` freezes the target, profiles and worker count for this run at `RUN/workflow`. Only `launch` starts the Yui workers.

After preparation, register **one active host heartbeat every 10 minutes
(600 seconds) in this same chat** with `automation_update`. Reuse a matching
heartbeat for this chat and run, updating its cadence, wake instruction and
notification settings if necessary. Include this README's absolute path and
the exact `RUN/workflow` path. Substitute the absolute script and run paths
in the wake instruction below.

> Run `python3 -B run_test.py observe RUN` once. Post a short status in Chinese with
> the phase, available completion counts and any fault or decision. **Report
> even when progress is unchanged.** For a running or paused case, end this
> turn after posting. At termination, follow the README to validate, report,
> clean up and remove the heartbeat.

Use the host-returned heartbeat ID as `HEARTBEAT_ID`. If registration fails,
report the prepared run and the error, leave the workers undispatched and end
the turn. Do not switch to foreground sleeping or polling.

```sh
python3 -B run_test.py launch RUN --heartbeat-id "$HEARTBEAT_ID"
python3 -B run_test.py observe RUN
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
what remains. Once the run is terminal, owned processes have exited, and final
reporting and cleanup are complete, delete its heartbeat using the saved ID and
record the deletion in `OWNER_MONITOR_STATE.json`. Post the final Chinese status
with the cleanup result and retained result location, then end the turn.
