# Pure-model benchmark

This is the entry point for the bare-model benchmark: its original run,
supplementary repair, preparation templates and reproduction instructions are
kept together here. The input paper is
[the complete Theorem 1 of the supplied manuscript](aim-518-kdv-log-loss.pdf).

To run a new experiment or rebuild the retained proof, start with
[REPRODUCE.md](REPRODUCE.md). No generated preparation file is needed to read
these instructions.

## Recorded results

| Stage | Recorded outcome | Wall time | Observed input + output tokens |
| --- | --- | ---: | ---: |
| [Original run: 20261028T154300Z-b21e5d9a](20261028T154300Z-b21e5d9a/README.md) | Compiled candidate; some external premises required source-faithfulness repair | 06:43:02 | 190,950,431 |
| [Supplement: 20261101T114606Z-5d3193f6](20261101T114606Z-5d3193f6/README.md) | Accepted repair of the original candidate, including independent evaluation | 04:23:01 | 57,597,770 |
| Original plus supplement | Recorded completed proof with explicit literature inputs | 11:06:03 | 248,548,201 |

The supplement is a continuation of the original mathematical result, not a
second independent from-scratch trial. It supplies faithful statements of the
original external theorems and proves the consequences needed by the unchanged
historical proof. The accepted chain still takes nine literature inputs as
explicit assumptions; it does not reprove those published theorems.

The recorded profile is gpt-6.1-sol / high / Standard, with one mathematical
author session per run. Supplementary repairs continued the same author
session; semantic evaluation used a separate context. Provider routing is
unverified and usage accounting is partial. Cached-input and reasoning-output
counters are subsets, not additional tokens. Exact times and accounting limits
are in the [accounting record](20261101T114606Z-5d3193f6/owner-records/accounting.json).

Start with the [accepted Lean sources](20261101T114606Z-5d3193f6/frozen-candidate-002/),
[source and bridge ledger](20261101T114606Z-5d3193f6/frozen-candidate-002/source-and-bridge-ledger.md),
[final acceptance report](20261101T114606Z-5d3193f6/review-003-output/acceptance-report.md)
and [final result](20261101T114606Z-5d3193f6/FINAL_RESULT.json).
These are retained experimental records; reorganizing the directories is not
a new mathematical review.

## Directory map

```text
pure-model-result/
  README.md                         Results and navigation; start here
  REPRODUCE.md                      Fresh experiment, supplement and rebuild
  prompt.py                         From-scratch author task renderer
  runner.py                         Historical direct-supervisor launcher
  skill_check.py                    This arm's own legacy-supervisor discovery
  aim-518-kdv-log-loss.pdf           This arm's byte-identical original paper
  tests/                            Bare-model launcher compatibility tests
  supplement-preparation/           Reusable supplement prompt and input settings
  20261028T154300Z-b21e5d9a/          Original candidate and execution evidence
  20261101T114606Z-5d3193f6/          Supplement, frozen candidates and review evidence
```

The [supplement preparation](supplement-preparation/README.md) is an input
template, not another run or a live execution status. The supplement's actual
status is in its result directory. The original and supplementary task prompts
remain with their respective run records.

The launcher and its test use this directory's discovery helper, not the Yui
benchmark's configuration, helpers or tests. Run `python3 -B -m unittest discover
-s tests -v` from this directory to check that compatibility without starting a
model. The Yui arm has its own independent entry under `../Yui/`.

## Location changes

The former sibling directories have been consolidated as follows:

| Former location under `benchmark/` | Current location under this directory |
| --- | --- |
| `supplement-preparation/` | `supplement-preparation/` |
| `pure-model-supplement/20261101T114606Z-5d3193f6/` | `20261101T114606Z-5d3193f6/` |

Raw logs, manifests, frozen sources and final reports retain their original
bytes, including historical absolute paths. Resolve those old locations with
the table above; use current README links for navigation. Build from a fresh
copy as described in REPRODUCE.md instead of overwriting archived build logs.
