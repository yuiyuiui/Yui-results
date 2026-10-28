# Theorem 1 benchmark startup

This repository contains inputs and benchmark startup material. The Yui runtime
is supplied by an independently installed skill named exactly `rigorous-proof`.
Neither the name nor location of a separate Yui source checkout is assumed.

## Installation check

Install the complete Yui skill using your host's supported skill installer or
local skill registration. A `SKILL.md` without its adjacent runtime directories
is insufficient. Then, from this repository root:

```sh
python3 -B benchmark/skill_check.py
```

The check asks the existing Codex app-server for `skills/list`, verifies the
exact enabled skill and required files, and reports its actual resolved entry.
It calls no model. Missing, disabled, incomplete or ambiguous installations fail
explicitly; there is no fallback to a neighboring repository. Codex is found on
PATH or through `YUI_CODEX_BINARY`/`--codex`. This discovery does not require the
paper to be inside the Yui repository or its installation.

## Yui full workflow

Explicitly ask the operator to use `$rigorous-proof` on this paper's complete
Theorem 1. Both profiles for this benchmark are `gpt-6.1-sol / high / Standard`.
Supply or confirm the per-case worker count; for the previously selected ten:

```sh
python3 -B benchmark/prepare_yui.py --workers 10
```

This returns `READY_FOR_SKILL_INVOCATION`, the exact installed skill item and
the invocation prompt. It does not start a model or count as a completed run.
The invoking Codex task reads that installed entry, explicitly uses
`$rigorous-proof`, freezes the full target and starts its normal full workflow.
No repository-relative path to Yui is used. See [operator rules](AGENTS.md).

The owner detaches actual mathematical work, registers one ten-minute host
heartbeat, saves its actual ID and ends the foreground turn. A pending handoff
is not an actual schedule. Each wake checks bounded metadata; unchanged checks
stay quiet unless periodic reports were explicitly requested. A host lacking
scheduled follow-up must disclose that limitation instead of idle polling.

## Direct-model arm

```sh
python3 -B benchmark/pure-model-result/runner.py \
  --work /absolute/path/to/fresh-direct-output --prepare-only
```

The runner performs the same mandatory installed-skill check, then loads only
`nl0/scripts/direct_runner.py` from that verified installation. It renders the
direct prompt with the actual paper, Lean and Mathlib paths. The supervisor
starts a single native session only when `--prepare-only` is omitted. The
measured direct session receives no Yui proof instructions and disables project
instructions, personal memories, plugins and delegation. Its normal incomplete
turns continue in the same session until an actual candidate, concrete blocker
or user cancellation. Compilation remains distinct from independent semantic
acceptance. No benchmark is started by installation or software tests.

Tool overrides remain `YUI_LEAN_ROOT`, `YUI_MATHLIB_ROOT`, `YUI_CODEX_BINARY`, or
the explicit `--lean`, `--mathlib`, `--codex` flags. Record actual transmitted and
observed profiles, qualifications, elapsed times and partial token coverage.
There is no imposed total time/token/call budget and no claimed speed advantage.
