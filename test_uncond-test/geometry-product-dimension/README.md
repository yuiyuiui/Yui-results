# Execute this unconditional test: Hausdorff product dimension

This README is the single execution entry for **this one problem**. In a fresh
Codex task, “Execute test_uncond-test/geometry-product-dimension/README.md” authorizes one fresh complete
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

Confirm the selected model profile in the owning chat. Prefer a permitted
ten-minute scheduled wakeup for status reports. If it cannot be established,
continue with an in-chat timed wait and the same ten-minute reports. Either
monitoring mode allows this run to proceed through preparation and dispatch.

## Scope and fixed configuration

- Source: [problem.md](problem.md), including its complete proof and approved
  interpretations. The target comes from its configured complete-target section,
  read fresh from this run's copy. Use no old target-selection JSON.
- Goal: **unconditional**, `full`, normal repair; 2basis → the same NL0/Audit A and Lean/Audit B → b2lean final closure.
- Both phase profiles use **gpt-6.1-sol / high / Standard** with no model
  fallback, an unlimited total budget and a 360-second native-call limit.
- Yui sizes the local review and Lean proof pools from the number of nodes
  in each phase.
- The registered checkout must match the `uncond-test` branch and the full Git commit
  in this entry’s settings. The prepared job must use the frozen public Yui workflow.
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

## 3. Prepare, dispatch once and report in this chat

```sh
python3 -B run_test.py prepare RUN
```

`prepare` freezes the reviewed target, phase profiles and automatic
concurrency policy under `RUN/workflow`. Only `launch` starts workers.

### Choose the monitoring mode

Use the same chat that prepared the job. Run exactly one of the two launch commands
below, replacing `RUN` with the absolute path returned by `begin`.

**Prefer a permitted ten-minute wakeup.** If host rules permit scheduling for
this run and a scheduling tool is available, establish one wakeup every
600 seconds in this same chat. Reuse a verified matching schedule or make
one creation attempt. For Codex hosts that permit this operation, use
`automation_update` with its current tool schema. Bind the exact README and
`RUN/workflow` paths, and request a Chinese status on every wake.

Only a confirmed matching active schedule and its actual returned ID count as
success. Store that ID as `HEARTBEAT_ID`, then launch once.

```sh
python3 -B run_test.py launch RUN --heartbeat-id "$HEARTBEAT_ID"
```

This records `RECORDED_BY_OWNER` in `RUN/OWNER_MONITOR_STATE.json`. After the
initial verification below, post the initial status and end this foreground turn.
Each scheduled wake reads status once, reports in Chinese and ends its turn.

**Fallback when a wakeup cannot be established.** If scheduling is
restricted, unavailable, unsuccessful or unconfirmed, report the reason once
in Chinese and continue with the same prepared run. Proceed directly with
in-chat observation. Run the plain launch command below.

```sh
python3 -B run_test.py launch RUN
```

This records `OWNER_CHAT_WAIT`. Omit `--heartbeat-id` entirely in this mode.
After initial verification, keep the current turn open and use the interruptible
`clock.sleep` tool with `duration_ms=600000`. After each wait, observe once
and report in Chinese, then wait again while the case remains live.

### Verify and observe the selected run

Both commands dispatch with `--detach`. Verify the dispatch receipt, controller
PID, start time and process group with one initial observation.

```sh
python3 -B run_test.py observe RUN
```

In either mode, run this observation once per ten-minute interval. Report the
phase, available counts and any fault or decision, even when progress is unchanged.
Follow the remaining sections for user decisions, cancellation and terminal
validation. A monitoring setup failure selects the fallback and continues the
authorized run. Mathematical or execution faults keep their own handling.

If dispatch is ambiguous, inspect the existing run's observation and dispatch
records before any further action. Never repeat an ambiguous launch. Previously
dispatched runs continue with their recorded owner and monitoring mode.

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
actual final b2lean proof and the portable delivery bound to the public workflow exit. It performs no new
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
what remains. Once the case is terminal, owned processes have exited, and the
reports and cleanup are complete, set `status` to `COMPLETED` in
`RUN/OWNER_MONITOR_STATE.json`. Preserve its recorded owner, run and mode. If
the run used a permitted host schedule, close that schedule by its saved
ID and record the outcome. Post the final Chinese status, cleanup result and
retained result location, then end the turn.
