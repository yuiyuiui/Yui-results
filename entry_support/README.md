# Shared entry support

The six exercise directories each own their executable README, problem and
settings. Start with that problem's README. This directory is mechanical
support, not a proof source or a separate execution entry.

- `exercise_entry.py`: source readback, preparation, one dispatch, observation,
  existing-evidence validation and cleanup for one problem.
- `owner_monitor.py` binds a single dispatch and its ten-minute observations to
  the chat that prepared the run.
- `common.py` and `skill_check.py`: paths, hashes, exact installed-skill discovery,
  runtime capabilities and final A/B/b2lean validation.
- `resource_cleanup.py`: terminal-run resource collection. Benchmark entries
  include the same standalone file so their snapshotted runtime is independent.
- `run_checks.py` and `process_ledger.py`: isolated software tests and cleanup of
  exact child identities on success, failure and catchable interruption.

Run software checks from the repository root:

```sh
python3 -B entry_support/run_checks.py entry_support/tests benchmark_cond/Yui/tests benchmark_uncond/Yui/tests benchmark_cond/pure-model-result/tests
```

To also test neutral preparation against a local compatible Yui installation,
set `YUI_TEST_INSTALLATION` to that installation's absolute root. These opt-in
tests prepare synthetic source and test neutral child processes; they never
dispatch a mathematical job or call a model. Without that variable, the tests
are explicitly skipped. No dependency installation or Lean build is required.

Every test group gets a private temporary root. The runner captures exact
PID/start/group identities, stops owned descendants and removes that root,
including hidden files and generated compilation caches. An ownership or exit
failure keeps its diagnostics and fails the test command. Unrelated processes,
shared Lean/mathlib and recorded mathematical results are outside this scope.
