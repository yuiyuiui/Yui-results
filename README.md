# Yui results and benchmark inputs

This independent repository stores mathematical inputs, benchmark startup
material and selected reference results. The harness is distributed separately
as the installed `$rigorous-proof` skill. A sibling Yui checkout is not required.
The harness source is maintained separately in [Yui](https://github.com/yuiyuiui/Yui).

- [`benchmark/`](benchmark/README.md): the supplied paper and installed-skill
  preflight, Yui invocation preparation and isolated direct-session startup.
- `test/`: the three supplied mathematical problem statements and one retained
  run directory per problem, including proofs, audits, native checks, execution
  records and raw runtime logs. These are archived attempts with their original
  identities and qualifications, not newly executed or relabeled results.

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
```
