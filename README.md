# Yui results and benchmark inputs

This private evidence repository stores supplied mathematical problems,
benchmark startup material and retained reference runs. The harness is
distributed separately as the installed `$rigorous-proof` skill, from
[Yui](https://github.com/yuiyuiui/Yui). No sibling checkout path is required.

- [`benchmark/`](benchmark/README.md) starts the canonical installed skill after
  explicit human authorization. Yui `main` now uses concise mathematical NL0;
  the earlier detailed workflow is preserved on
  [nl0-detail](https://github.com/yuiyuiui/Yui/tree/nl0-detail).
  New outputs belong in `benchmark/results/<run-id>/`.
- `benchmark/pure-model-result/` retains the historical direct-model evidence.
  It remains unchanged and is excluded from fresh Yui construction inputs.
- `test/` retains the three problem statements and archived attempts with their
  original runtime identities, gate reports, faults, costs and qualifications.
  Historical runs retain their original workflow and outcome. The earlier
  paused Lie run was explicitly cancelled and its owned resources retired.
  The 2026-10-31 translation-only retest used complete copied accepted NL0/A
  inputs and canonical Yui commit `372046341c3523a0939d19df218b02d5b0bb67eb`.
  All three translations passed bound-artifact validation; their owned process
  groups exited and the completed monitor was deleted. See the
  [final report](test/geometry-product-dimension/rigorous-proof/20261031T112807Z-nl02lean-retest-6348e09d/nl02lean/FINAL_REPORT.md)
  for actual gates, timings and partial usage qualifications.

The duplicate `benchmark-v2/` and `test-v2/` trees were removed from the current
checkout after a complete eligible archive was committed and pushed. Their
original files remain available at archive commit `21e7e3ddadfa1ad8a4b54007b9c3ffb6788aacaf`:

- [V2 benchmark archive](https://github.com/yuiyuiui/Yui-results/tree/21e7e3ddadfa1ad8a4b54007b9c3ffb6788aacaf/benchmark-v2)
- [V2 three-problem test archive](https://github.com/yuiyuiui/Yui-results/tree/21e7e3ddadfa1ad8a4b54007b9c3ffb6788aacaf/test-v2)

For example, inspect a retained file without restoring a second working tree:

```sh
git show 21e7e3ddadfa1ad8a4b54007b9c3ffb6788aacaf:test-v2/README.md
```

Historical source paths, snapshots and receipt identities are kept as recorded.
Use actual gate reports to determine acceptance: a directory, a normal model
turn or compilation alone does not establish completion of the original target.
Credentials, private runtime homes, caches and environment files are excluded
from the Git archive. Removing a directory from the current checkout does not
remove its archived Git history.

Software startup checks make no model request:

```sh
python3 -B -m unittest discover -s benchmark/tests -v
```

Preparation is not benchmark execution. Follow `benchmark/AGENTS.md` and obtain
explicit start authorization before a fresh mathematical run.
