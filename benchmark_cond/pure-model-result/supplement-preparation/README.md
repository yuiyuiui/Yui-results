# Bare-model supplement preparation

This directory preserves the reusable preparation template for the
[completed supplementary run](../20261101T114606Z-5d3193f6/README.md).
`PREPARED_NOT_STARTED` in settings describes the template, not the status of
that historical run. These files do not authorize another launch. Start at the
[pure-model index](../README.md) and [reproduction instructions](../REPRODUCE.md).

This preparation contains only:

- `prompt.md`: the mathematical task template, including the four requested outcomes and strict final external-input equivalence.
- `settings.json`: original-input references and hashes, requested model configuration, pinned toolchain and the unstarted execution contract.

All input paths in settings are relative to `pure-model-result/`, the parent of
this preparation directory. Original papers, the historical bare-model proof
and its original cost records remain in their existing locations. Primary PDF
bytes in the historical owner-records directory are permitted; surrounding
audit reports and judgments are not mathematical inputs.

At an explicitly authorized future launch, validate the input hashes, choose a fresh output directory, stage the allowed inputs, render the prompt placeholders with actual absolute paths, and record actual model configuration, elapsed time and native token usage. Use the ordinary native tool environment; do not add a custom OS sandbox or silently invoke the historical `runner.py` / Yui direct supervisor.

There is no imposed total time, token, model-call or iteration budget. A fixed one-turn completion deadline is not part of the task. The author must not present a partial source inventory, unproved bridges or an unchanged conditional proof as completion. Any additional interaction must remain explicit in the recorded experiment protocol; these files implement no automatic continuation or verifier-feedback mechanism.

Final acceptance checks the actual complete input signature against the full original external theorem statements. Sound weaker consequences belong inside the checked proof. Already equivalent ports may be reused without redundant bridge work.

No run ID, session/process identity, runtime home, authentication copy, execution log, supplementary proof, audit result or supplementary cost measurement is retained here. The original Yui result and original bare-model candidate are separate, unchanged historical records.
