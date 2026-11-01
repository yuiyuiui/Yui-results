# Yui test and benchmark results

This repository stores test and benchmark results for [Yui](https://github.com/yuiyuiui/Yui), a workflow for developing an existing natural-language mathematical proof into an audited Lean proof.

To run these locally, complete [local setup](#local-setup), then use the [benchmark](#reproduce-the-benchmark) or [test](#reproduce-the-tests) prompts below in fresh local Codex chats opened at this repository root.

## Benchmark

| Method | Elapsed time | Observed input + output tokens | Results |
| --- | ---: | ---: | --- |
| **Yui** | **04:09:26** | **282,760,473** | [Full workflow](benchmark/results/20261031T212422Z-533b379994/) |
| **Pure model, including supplement** | **11:06:03** | **248,548,201** | [Completed result](benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/FINAL_REPORT.md) |

**In this recorded benchmark, Yui completed the task 2.67× as fast as the pure model, using 13.8% more observed tokens.** The pure-model total includes its original attempt, supplementary repair and acceptance review.

The input is the repository author's [natural-language proof](benchmark/aim-518-kdv-log-loss.pdf) of [AIM problem 518: removing the logarithmic loss in the Li–Wu KdV integrator](https://github.com/MColbrook/AIM/blob/main/problems/518-kdv-integrator-logarithmic-loss.md), listed as **SOLVED** by the AIM repository following independent AI review. The benchmark compares both approaches on the paper's complete Theorem 1 and tests Yui's reliability on a larger proof.

Despite the [original prompt](benchmark/pure-model-result/20261028T154300Z-b21e5d9a/prompt.md), some external theorem statements in the pure-model proof were weakened consequences of the originals. The [supplement](benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/) supplies faithful original statements, proves the missing Lean bridges and connects them to the unchanged original proof. The [completed Lean project](benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/frozen-candidate-002/) compiled and passed the recorded acceptance review. Both approaches retain the cited literature theorems as explicit inputs.

**Configuration:** all model stages requested **gpt-6.1-sol / high / Standard**, using clean background Codex CLI processes. Yui allowed **20 local workers** in this benchmark; pure-model construction used one author session per run. These are recorded workflow timings with different parallelism. Usage is `PARTIAL`; token totals count observed input plus output, with cached and reasoning tokens already included. Detailed records: [Yui](benchmark/results/20261031T212422Z-533b379994/FINAL_OUTCOME.json), [pure model](benchmark/pure-model-supplement/20261101T114606Z-5d3193f6/owner-records/accounting.json), and [startup instructions](benchmark/README.md).

### Reproduce the benchmark

After [setup](#local-setup), paste this into a fresh local Codex chat to run the **Yui arm**:

```text
Use $rigorous-proof to start a fresh full Yui benchmark now. Follow benchmark/AGENTS.md and benchmark/settings.json, regenerating and verifying local preparation first.
Use only benchmark/aim-518-kdv-log-loss.pdf as mathematical input, preserving the complete Theorem 1. Use gpt-6.1-sol/high/Standard for both phases and 20 local workers.
Run detached through NL0/Audit A and Lean/Audit B. Save to a new benchmark/results/<run-id>/ directory and report acceptance, elapsed time and token usage. Do not use earlier results as proof inputs.
```

For the **pure-model arm**, use a separate fresh local Codex chat and paste:

```text
Independently rerun the pure-model benchmark now on benchmark/aim-518-kdv-log-loss.pdf, targeting the complete Theorem 1.
Use one clean native Codex CLI author session with gpt-6.1-sol/high/Standard. Render the task from benchmark/pure-model-result/prompt.py using this machine's paths; give the author only that task, the paper, its cited sources and pinned Lean/Mathlib. Do not give it Yui rules, personal skills/memories or earlier results.
Save the exact prompt, configuration, elapsed time, native token records and proof under a new benchmark/pure-model-result/<run-id>/. Independently check full target and external-theorem fidelity; continue the same author session for any required repairs, recording repair and acceptance-review costs separately in the total.
```

## Tests

The three test problems cover different fields, at roughly advanced undergraduate to graduate level. They test Yui's reliability across the complete natural-language proof, review, Lean translation and final acceptance workflow.

Only the latest full run for each problem is retained in the current checkout. All three used the same harness runtime as Yui commit [`d657ecb9`](https://github.com/yuiyuiui/Yui/commit/d657ecb93d7586d42c17e05cebbaa6cf7d194232), with **10 local workers per case**, and finished with `WORKFLOW-PASSED` and `AUDIT-B-PASSED`.

| Problem | Elapsed time | Observed tokens | Result directory |
| --- | ---: | ---: | --- |
| Analysis / geometry: Hausdorff dimension of a product with an interval | 00:30:54 | 15,080,248 | [geometry-product-dimension](test/geometry-product-dimension/rigorous-proof/20261101-fresh-full-18b3e2e0bf/) |
| Algebra: irreducibility after reduction of an admissible sl2 lattice | 00:50:36 | 20,297,548 | [lie-module-irreducibility](test/lie-module-irreducibility/rigorous-proof/20261101-fresh-full-18b3e2e0bf/) |
| PDE: conservation of energy for a sphere-valued wave map | 00:27:18 | 11,489,484 | [wave-map-energy](test/wave-map-energy/rigorous-proof/20261101-fresh-full-18b3e2e0bf/) |

The three cases ran concurrently. These usage records are `PARTIAL`. (Occasional network instability and background-to-foreground reporting can affect token and timing accounting; the size of any discrepancy has not been quantified.)

Each problem's `problem.md` records its source, complete target and approved interpretations. Each result directory includes:

1. `OWNER_FINAL_REPORT.json`: the final verification summary, including acceptance status and measurement qualifications.
2. `case-result.json`: Yui's machine-readable workflow result and usage summary.
3. `Proof.lean`: the assembled final Lean proof, under `nl0-to-lean/.../workflow/audit-b/`.
4. Reviews: the proof reviews and acceptance checks for the natural-language proof and Lean translation.
5. Execution records: the run configuration, process records, logs, timing and token accounting.

Older runs remain in Git history.

### Reproduce the tests

After [setup](#local-setup), paste this into a fresh local Codex chat:

```text
Use $rigorous-proof to rerun all three test/*/problem.md cases concurrently through the full NL0/Audit A and Lean/Audit B workflow.
Use gpt-6.1-sol/high/Standard for both phases and 10 local workers per case. Generate fresh target selections from the problem statements on this machine; do not reuse old target-selection JSON or results as proof inputs.
Start now, detached. Save each fresh run under its problem's rigorous-proof/<run-id>/ without overwriting existing results, and report each case's acceptance, elapsed time and token usage.
```

## Local setup

Use macOS with an authenticated Codex CLI and the [Yui runtime prerequisites](https://github.com/yuiyuiui/Yui#runtime), including Python, ripgrep and the pinned Lean 4.32.2/Mathlib environment. Install the **complete Yui repository** as `$rigorous-proof`, not just `SKILL.md`. To install the updated documentation and logo with the same harness runtime as the recorded runs, ask local Codex once:

```text
Install https://github.com/yuiyuiui/Yui at commit d657ecb93d7586d42c17e05cebbaa6cf7d194232 as the rigorous-proof skill in ~/.agents/skills/rigorous-proof, keeping the entire repository together. Check its README prerequisites and run its doctor check; do not start any proof jobs yet. If this exact skill is already installed, use that installation without creating a duplicate.
```

The installation location follows [Codex's local skill documentation](https://developers.openai.com/codex/skills/#where-to-save-skills). Confirm `$rigorous-proof` is available before running a prompt; restart Codex if it is not detected. Fresh runs can produce different proofs, repair steps, timings and token totals.
