# Yui results and benchmark inputs

This independent repository stores mathematical inputs, benchmark startup
material and selected reference results. The harness is distributed separately
as the installed `$rigorous-proof` skill. A sibling Yui checkout is not required.
The harness source is maintained separately in [Yui](https://github.com/yuiyuiui/Yui).

- [`benchmark/`](benchmark/README.md): the supplied paper and installed-skill
  preflight, Yui invocation preparation and isolated direct-session startup.
- `test/`: the three supplied mathematical problem statements. The current
  initial repository does not include historical successful run directories;
  user-deleted runs have not been restored or relabeled as new results.

Before running the benchmark, follow its installation check and operator rules.
Check result scope using actual NL0/Audit A, standalone Lean/native evidence and
independent Audit B. Do not infer mathematical success from a directory, a
normal model turn, a self-report or compilation alone.

Keep concise proof/results and their provenance available for reference. Large
raw runtime logs and private model state should be reviewed separately before
archival; credentials, caches and environment files are excluded from Git.
Committing an old source-retrieval check does not establish a new full workflow.

Software startup controls run without a model:

```sh
python3 -B -m unittest discover -s benchmark/tests -v
```
