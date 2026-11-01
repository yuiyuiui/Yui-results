# Original pure-model run

This directory preserves the original compiled candidate, whose external premises required later source-faithfulness repair. Its recorded elapsed time is **6 h 43 min**, with **190,950,431 observed input + output tokens**. For the completed strict-input proof and total repair costs, see the [accepted supplement](../../pure-model-supplement/20261101T114606Z-5d3193f6/README.md).

## Original artifacts

- [Exact generated task prompt](prompt.md).
- [Original Proof.lean](Proof.lean).
- [Author correspondence record](correspondence.md) and [original warnings](warn.json).
- [Execution result and reported usage](execution-result.json).
- [Completion check](completion-check.json).
- [Build verification](build-verification.json).

## Raw execution evidence

- [Native CLI event stream](turn-0001.jsonl), including the terminal usage event.
- [Native CLI stderr](turn-0001.stderr).
- [Non-sensitive native-home configuration](.runtime-home/config.toml).
- [Native session record](.runtime-home/sessions/2026/10/28/rollout-2026-10-28T23-43-34-01a1832e-54ee-7c02-a378-8260250e420c.jsonl).

Sum `input_tokens` and `output_tokens` from the single `turn.completed` event in the CLI stream to reproduce the original observed token total. Cached-input and reasoning-output fields are already subsets. The archive excludes authentication, account databases, generated skills, locks, temporary state and compiled Lean caches. Original event and evidence bytes have not been edited for this publication index.
