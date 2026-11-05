# Yui test and benchmark results

This repository stores test and benchmark results for [Yui](https://github.com/yuiyuiui/Yui), a workflow for developing an existing natural-language mathematical proof into an audited Lean proof.

To run these locally, complete [local setup](#local-setup), then use the [benchmark](#reproduce-the-benchmark) or [test](#execute-one-problem-in-a-fresh-task) prompts below in fresh local Codex chats opened at this repository root.

For all six tests and both Yui benchmarks, start the foreground task with
**gpt-6.1-sol / high / Standard**. This trusted checkout loads the defaults from
[its project configuration](.codex/config.toml). The paired Yui checkout also
sets them for chats opened there. When using `create_thread`, select
`model="gpt-6.1-sol"` and `thinking="high"` at creation. Give the task only
`Execute <path>/README.md`, using the absolute entry path when starting in Yui.

Each entry registers a ten-minute heartbeat in its owning chat before launching
the detached workers. The owner posts one short Chinese status on every wake,
including unchanged progress, and ends the turn between checks.

## Benchmark

| Method | Elapsed time | Observed input + output tokens | Results |
| --- | ---: | ---: | --- |
| **Yui** | **04:09:26** | **282,760,473** | [Full workflow](benchmark_cond/Yui/results/20261031T212422Z-533b379994/) |
| **Pure model, including supplement** | **11:06:03** | **248,548,201** | [Pure-model results](benchmark_cond/pure-model-result/README.md) |

**In this recorded benchmark, Yui completed the task 2.67× as fast as the pure model, using 13.8% more observed tokens.** The pure-model total includes its original attempt, supplementary repair and acceptance review.

The input is the repository author's [natural-language proof](benchmark_cond/Yui/aim-518-kdv-log-loss.pdf) of [AIM problem 518: removing the logarithmic loss in the Li–Wu KdV integrator](https://github.com/MColbrook/AIM/blob/main/problems/518-kdv-integrator-logarithmic-loss.md), listed as **SOLVED** by the AIM repository following independent AI review. The benchmark compares both approaches on the paper's complete Theorem 1 and tests Yui's reliability on a larger proof.

Despite the [original prompt](benchmark_cond/pure-model-result/20261028T154300Z-b21e5d9a/prompt.md), some external theorem statements in the pure-model proof were weakened consequences of the originals. The [supplement](benchmark_cond/pure-model-result/20261101T114606Z-5d3193f6/) supplies faithful original statements, proves the missing Lean bridges and connects them to the unchanged original proof. The [completed Lean project](benchmark_cond/pure-model-result/20261101T114606Z-5d3193f6/frozen-candidate-002/) compiled and passed the recorded acceptance review. Both approaches retain the cited literature theorems as explicit inputs.

**Configuration:** all model stages requested **gpt-6.1-sol / high / Standard**, using clean background Codex CLI processes. Yui allowed **20 local workers** in this benchmark; pure-model construction used one author session per run. These are recorded workflow timings with different parallelism. Usage is `PARTIAL`; token totals count observed input plus output, with cached and reasoning tokens already included. Detailed records: [Yui](benchmark_cond/Yui/results/20261031T212422Z-533b379994/FINAL_OUTCOME.json), [pure model](benchmark_cond/pure-model-result/20261101T114606Z-5d3193f6/owner-records/accounting.json), and [Yui entry](benchmark_cond/Yui/README.md).

### Reproduce the benchmark

After [setup](#local-setup), paste this into a fresh local Codex chat to run the **Yui arm**:

```text
Execute benchmark_cond/Yui/README.md.
```

For the **pure-model arm**, start from its [results and instructions](benchmark_cond/pure-model-result/README.md). Use a separate fresh local Codex chat and paste:

```text
Run a fresh from-scratch pure-model benchmark now. Start at benchmark_cond/pure-model-result/README.md and follow section 1 of REPRODUCE.md, targeting the complete Theorem 1 of benchmark_cond/pure-model-result/aim-518-kdv-log-loss.pdf.
Use one clean native author session with gpt-6.1-sol/high/Standard and pinned Lean/Mathlib. Do not give the author Yui proof rules, personal skills/memories or earlier results.
Save the exact inputs, prompt, configuration, elapsed time, native token records, proof and separate acceptance review under a new benchmark_cond/pure-model-result/<run-id>/.
```

## Tests

The three test problems cover different fields, at roughly advanced undergraduate to graduate level. They test Yui's reliability across the complete natural-language proof, review, Lean translation and final acceptance workflow.

Only the latest full run for each problem is retained in the current checkout. All three used the same harness runtime as Yui commit [`adf65d18`](https://github.com/yuiyuiui/Yui/commit/adf65d18c810ffa9105e03a4b89b2fb5ad441e26), with **10 local workers per case**, and finished with `WORKFLOW-PASSED` and `AUDIT-B-PASSED`.

| Problem | Elapsed time | Observed tokens | Result directory |
| --- | ---: | ---: | --- |
| Analysis / geometry: Hausdorff dimension of a product with an interval | 00:30:54 | 15,080,248 | [geometry-product-dimension](test_cond/geometry-product-dimension/rigorous-proof/20261101-fresh-full-18b3e2e0bf/) |
| Algebra: irreducibility after reduction of an admissible sl2 lattice | 00:50:36 | 20,297,548 | [lie-module-irreducibility](test_cond/lie-module-irreducibility/rigorous-proof/20261101-fresh-full-18b3e2e0bf/) |
| PDE: conservation of energy for a sphere-valued wave map | 00:27:18 | 11,489,484 | [wave-map-energy](test_cond/wave-map-energy/rigorous-proof/20261101-fresh-full-18b3e2e0bf/) |

The three cases ran concurrently. These usage records are `PARTIAL`. (Occasional network instability and background-to-foreground reporting can affect token and timing accounting; the size of any discrepancy has not been quantified.)

Each problem's `problem.md` records its source, complete target and approved interpretations. Each result directory includes:

1. `OWNER_FINAL_REPORT.json`: the final verification summary, including acceptance status and measurement qualifications.
2. `case-result.json`: Yui's machine-readable workflow result and usage summary.
3. `Proof.lean`: the assembled final Lean proof, under `nl0-to-lean/.../workflow/audit-b/`.
4. Reviews: the proof reviews and acceptance checks for the natural-language proof and Lean translation.
5. Execution records: the run configuration, process records, logs, timing and token accounting.

Older runs remain in Git history.

### Execute one problem in a fresh task

Each problem owns its own README, source, settings and run directory. A fresh
task needs only `Execute <path>/README.md`; no separate generated task prompt
or second start message is required.

| Goal | Problem entry |
| --- | --- |
| Conditional Lean, full workflow | [test_cond/geometry-product-dimension/README.md](test_cond/geometry-product-dimension/README.md) |
| Conditional Lean, full workflow | [test_cond/lie-module-irreducibility/README.md](test_cond/lie-module-irreducibility/README.md) |
| Conditional Lean, full workflow | [test_cond/wave-map-energy/README.md](test_cond/wave-map-energy/README.md) |
| Unconditional Lean, full workflow | [test_uncond/geometry-product-dimension/README.md](test_uncond/geometry-product-dimension/README.md) |
| Unconditional Lean, full workflow | [test_uncond/lie-module-irreducibility/README.md](test_uncond/lie-module-irreducibility/README.md) |
| Unconditional Lean, full workflow | [test_uncond/wave-map-energy/README.md](test_uncond/wave-map-energy/README.md) |

For example:

```text
Execute test_uncond/wave-map-energy/README.md.
```

The conditional benchmark has its existing entry at
[benchmark_cond/Yui/README.md](benchmark_cond/Yui/README.md). Its current settings
select NL0/Audit A only; the retained full-workflow numbers above are historical.
The unconditional benchmark has a separate full-workflow entry at
[benchmark_uncond/Yui/README.md](benchmark_uncond/Yui/README.md), with no bare-model
arm. Both entries include terminal validation, reporting and owned resource
cleanup. The bare-model arm remains exclusively under `benchmark_cond` with its
existing reproduction procedure.

Every new run binds the current original input and creates a fresh target
selection. Archived target selections, runtime snapshots and absolute paths in
historical records are preserved as evidence, not rewritten or reused as fresh
construction inputs. All Yui entries retain useful proof/audit/source evidence
while removing only owned disposable processes, caches and native scratch.

## Local setup

Use macOS with an authenticated Codex CLI and follow [Yui's local setup guide](https://github.com/yuiyuiui/Yui/blob/main/docs/setup.md) for the matching Code Mode helper, Python, ripgrep and pinned Lean 4.32.2/Mathlib environment. Install the **complete Yui repository** as `$rigorous-proof`, not just `SKILL.md`. Historical results identify their original runtime. For a new run, install the complete intended Yui version; unconditional entries require its 2basis/b2lean support. Do not silently replace an installed runtime during a run. For example:

```text
Install https://github.com/yuiyuiui/Yui from its uncond branch as the rigorous-proof skill in ~/.agents/skills/rigorous-proof, keeping the entire repository together. Check its README prerequisites and run its doctor check; do not start any proof jobs yet. If this exact skill is already installed, use that installation without creating a duplicate.
```

The installation location follows [Codex's local skill documentation](https://developers.openai.com/codex/skills/#where-to-save-skills). Confirm `$rigorous-proof` is available before running a prompt; restart Codex if it is not detected. Fresh runs can produce different proofs, repair steps, timings and token totals.

## License

Original contributor-owned code, Lean proofs, documentation and records are available under the [MIT license](LICENSE). External papers, images, quoted statements and other third-party material retain their own terms; see [third-party notices](#third-party-notices).

## Third-party notices

The [MIT license](LICENSE) applies to original material owned by this repository's contributors, including original code, Lean proofs, documentation and measurement records. It does not relicense external papers, quoted exercise statements, page images, source excerpts, embedded third-party instructions or dependencies.

### Benchmark papers

The retained benchmark PDFs represent these documents, with repeated copies in run evidence:

| Document | Source and rights boundary |
| --- | --- |
| Kaiwen Jin, *Removing the logarithmic loss in the Li-Wu KdV integrator* | Repository author's supplied manuscript, including `benchmark_cond/Yui/aim-518-kdv-log-loss.pdf`, the pure-model arm's byte-identical copy and copies named `target.pdf`. Original author-owned content is under MIT; quoted third-party material retains its own terms. |
| Buyang Li and Yifei Wu, *An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below H1* | Copies named `li-wu.pdf` and the corresponding source-access/input-byte files. [Author manuscript](https://www.polyu.edu.hk/ama/profile/byli/FoCM-3.pdf); [arXiv record](https://arxiv.org/abs/2206.09320). Excluded from MIT; permission to redistribute the retained manuscript has not been verified. |
| Anatoli V. Babin, Alexei A. Ilyin and Edriss S. Titi, *On the regularization mechanism for the periodic Korteweg-de Vries equation* | Copies named `babin-ilyin-titi.pdf` and the corresponding source-access/input-byte files. [arXiv source record](https://arxiv.org/abs/0910.1389v2). Excluded from MIT; the source record links to an [arXiv non-exclusive distribution license](https://arxiv.org/licenses/nonexclusive-distrib/1.0/license.html), not a project-wide MIT grant. Separate redistribution permission has not been established here. |

Page renderings, extracted text and quotations from these papers retain the underlying material's rights. Original source/version records remain with each run. Retaining a source for audit does not establish a right to redistribute it; this notice does not claim complete publication clearance.

### Exercise statements and source excerpts

The three test `problem.md` files identify and quote exercises from Stein and Shakarchi's *Real Analysis*, Humphreys' *Introduction to Lie Algebras and Representation Theory*, and Evans' *Partial Differential Equations*. Those quoted statements retain their authors' and publishers' rights. The project's own interpretations, solutions and formalizations are licensed only to the extent that contributors hold the relevant rights.

Mathlib and other dependency excerpts retain their upstream attribution and licenses; see [Mathlib's license](https://github.com/leanprover-community/mathlib4/blob/master/LICENSE). Archived Yui runtime code is original project code, but its external dependencies are not relicensed by this repository. Raw execution records can contain quoted third-party text or tool instructions; MIT covers the contributors' original portions, not those embedded materials.
