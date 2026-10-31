# Yui results and benchmark inputs

This independent repository stores mathematical inputs, benchmark startup
material and selected reference results. The harness is distributed separately
as the installed `$rigorous-proof` skill. A sibling Yui checkout is not required.
The harness source is maintained separately in [Yui](https://github.com/yuiyuiui/Yui).

- [`benchmark/`](benchmark/README.md): retained original benchmark startup for
  the installed `$rigorous-proof`; new runs belong in `benchmark/results/`.
  Its retained `pure-model-result/` is historical evidence, excluded from new
  Yui construction inputs and left unchanged.
- [`benchmark-v2/`](benchmark-v2/README.md): self-contained V2 startup for the
  installed `$rigorous-proof-v2`, with its own identical input and matched setup;
  new runs belong in `benchmark-v2/results/`. No sibling benchmark import is
  required. The owner writes the post-termination comparison here according to
  [the comparison plan](benchmark-v2/COMPARISON_PLAN.md).
- `test/`: the three supplied mathematical problem statements and retained
  attempt directories, including proofs, audits, native checks, execution
  records and raw runtime logs. These are archived attempts with their original
  identities and qualifications, not newly executed or relabeled results.

- [`test-v2/`](test-v2/README.md): the historical three-problem V2 inputs and actual run evidence,
  with original identities, gates, faults and usage records. These are archives,
  not an unstarted test queue.

Before running the benchmark, follow its installation check and operator rules.
Check result scope using actual NL0/Audit A, standalone Lean/native evidence and
independent Audit B. Do not infer mathematical success from a directory, a
normal model turn, a self-report or compilation alone.

Keep proof/results and their provenance available for reference. The retained
test runs include reviewed raw logs as part of this dedicated evidence archive;
credentials, private runtime homes, caches and environment files remain
excluded by the repository's ignore rules.
Committing an old source-retrieval check does not establish a new full workflow.

Software startup controls run without a model:

```sh
python3 -B -m unittest discover -s benchmark/tests -v
python3 -B -m unittest discover -s benchmark-v2/tests -v
```

Neither preparation nor software controls start a mathematical benchmark.
Fresh-task dispatch waits for the human's explicit start authorization.

This commit is the retained-evidence checkpoint before consolidating the two
software versions. The last paused V1 test was explicitly cancelled, its monitor
was removed, both test tasks were archived, and all 62 verified owned local
process identities/groups exited. Scientific artifacts retain their original
qualification; cancellation does not turn an unfinished proof into a PASS.
