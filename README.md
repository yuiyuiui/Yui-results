# Yui test and benchmark results

This repository stores test and benchmark results for
[Yui](https://github.com/yuiyuiui/Yui), a workflow for developing an existing
natural-language mathematical proof into an audited Lean proof.

## Tests

The three test problems cover different fields, at roughly advanced
undergraduate to graduate level. They test Yui's reliability across the complete
natural-language proof, review, Lean translation and final acceptance workflow.

Only the latest full run for each problem is retained in the current checkout.
All three use Yui commit
[`9b73a3dd`](https://github.com/yuiyuiui/Yui/commit/9b73a3dd53c38a5785fe3f3e4f21f7367b57a825),
with 10 local workers per case, and finished with `WORKFLOW-PASSED` and
`AUDIT-B-PASSED`.

| Problem | Elapsed time | Observed tokens | Result directory |
| --- | ---: | ---: | --- |
| Analysis / geometry: Hausdorff dimension of a product with an interval | 00:30:54 | 15,080,248 | [geometry-product-dimension](test/geometry-product-dimension/rigorous-proof/20261101-fresh-full-18b3e2e0bf/) |
| Algebra: irreducibility after reduction of an admissible sl2 lattice | 00:50:36 | 20,297,548 | [lie-module-irreducibility](test/lie-module-irreducibility/rigorous-proof/20261101-fresh-full-18b3e2e0bf/) |
| PDE: conservation of energy for a sphere-valued wave map | 00:27:18 | 11,489,484 | [wave-map-energy](test/wave-map-energy/rigorous-proof/20261101-fresh-full-18b3e2e0bf/) |

The three cases ran concurrently: the batch took about 50 minutes 36 seconds,
with 46,867,280 observed tokens in total. These usage records are `PARTIAL`.
Each problem's `problem.md` records its source, complete target and approved
interpretations. Each result directory includes `OWNER_FINAL_REPORT.json`,
`case-result.json`, the proof, reviews and execution records. Older runs remain
in Git history.

## Benchmark

The benchmark input is the repository author's
[natural-language proof](benchmark/aim-518-kdv-log-loss.pdf) of
[AIM problem 518: removing the logarithmic loss in the Li–Wu KdV integrator](https://github.com/MColbrook/AIM/blob/main/problems/518-kdv-integrator-logarithmic-loss.md).
The AIM repository lists the problem as **SOLVED** following review of the
submitted solution. Its status page describes the review as independent AI
review, rather than human peer review or Lean verification.

The benchmark compares Yui and a bare model on the paper's complete Theorem 1,
and tests Yui's reliability on a larger proof. Inputs, configurations, outputs
and measurement records are under [`benchmark/`](benchmark/).

- **Yui:** [full workflow result](benchmark/results/20261031T212422Z-533b379994/),
  using the same Yui commit as the tests. The run finished with
  `WORKFLOW-PASSED` and `AUDIT-B-PASSED`; its
  [final Lean proof](benchmark/results/20261031T212422Z-533b379994/nl0-to-lean/0002/workflow/audit-b/Proof.lean)
  and [final report](benchmark/results/20261031T212422Z-533b379994/FINAL_REPORT.zh.md)
  are retained.
- **Bare model, original run:**
  [result directory](benchmark/pure-model-result/20261028T154300Z-b21e5d9a/)
  and [original prompt](benchmark/pure-model-result/20261028T154300Z-b21e5d9a/prompt.md).
- **Bare model, accepted supplement:**
  [result directory](benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/),
  [accepted Lean project](benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/frozen-candidate-002/),
  and [final result and accounting report](benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/FINAL_REPORT.md).

### Why the bare-model result needed a supplement

Although the original prompt required faithful external theorem statements,
several external premises in the original bare-model Lean proof were weakened
or specialized consequences of the cited theorems, rather than strictly
equivalent formalizations of their full statements. Compiling that proof did
not supply the missing derivations from the original external theorems.

The supplement states the full original external inputs and proves the missing
Lean bridges to the historical proof's premises. Seven premises needed proved
bridges; two already equivalent premises were retained directly. It then
applies the unchanged original proof to obtain the complete target. The final
entry point is
[`CompletedProof.lean`](benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/frozen-candidate-002/CompletedProof.lean),
within a multi-file Lean project. All 11 delivered modules compiled in both the
author's build and the independent verification build. Separate-context model
review accepted the source correspondence, bridges and complete target.

In both arms, literature theorems remain explicit inputs: the Lean proof checks
the derivation from those inputs to the target. Their correspondence with the
natural-language sources is reviewed separately.

### Configuration and resource use

All measured model stages requested **gpt-6.1-sol / high / Standard**, with no
model fallback. Tasks used clean background Codex CLI processes and the Codex
service, with recorded prompts and configurations. The provider's actual
serving model and service tier were not independently exposed. Yui allowed 20
local workers in the benchmark; the bare-model construction used one native
author session per run. The supplement continued its author session after
independent acceptance feedback.

| Benchmark stage | Elapsed time | Observed input + output tokens |
| --- | ---: | ---: |
| **Yui, complete workflow** | **04:09:26** | **282,760,473** |
| Bare model, original result with external-input drift | 06:43:02 | 190,950,431 |
| Bare model, supplement through acceptance | 04:23:01 | 57,597,770 |
| **Bare model, original + accepted supplement** | **11:06:03** | **248,548,201** |

Times are recorded elapsed wall times, rounded to the nearest second. The
bare-model total adds the historical run and the accepted supplement. The
Yui time runs from dispatch to workflow termination, excluding owner preparation
and final reporting. The
supplement includes author work, independent evaluation, verification and
intervening waits. Its observed tokens comprise 43,833,123 author tokens and
13,764,647 evaluator tokens. The corresponding sums of native session intervals
are 03:42:30 and 00:30:34; these are already inside the supplement's elapsed
time and are not added again.

Token totals count observed input plus output; cached-input and reasoning-output
counts are subsets, not extra tokens. Accounting is `PARTIAL`: unexposed usage,
operator overhead and costs of earlier cancelled and deleted attempts are not
fully measurable and are not included as known zeroes. Execution records retain
transport and reporting faults. Shared host/account resources, different
parallelism and the post-hoc repair procedure limit causal speed comparisons.

The numerical sources are Yui's
[`FINAL_OUTCOME.json`](benchmark/results/20261031T212422Z-533b379994/FINAL_OUTCOME.json)
and the supplement's
[`accounting.json`](benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/owner-records/accounting.json).
See the [benchmark instructions](benchmark/README.md) for preparation and
execution details.
