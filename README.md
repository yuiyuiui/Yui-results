# Yui test and benchmark results

This repository contains conditional and unconditional Lean formalizations of three mathematical exercises, and a benchmark comparing [Yui](https://github.com/yuiyuiui/Yui) with a single proof author. Each exercise has its own input, execution instructions and recorded result.

## Exercise results

Each cell links to the recorded result and gives the Yui case time (hh:mm:ss) and observed input plus output tokens. Token coverage was partial in all six runs.

| Problem | Conditional · time / tokens | Unconditional · time / tokens |
| --- | ---: | ---: |
| Hausdorff dimension of a product with an interval | [00:30:54 / 15,080,248](test_cond/geometry-product-dimension/rigorous-proof/20261101-fresh-full-18b3e2e0bf/OWNER_FINAL_REPORT.json) | [01:08:46 / 17,090,500](test_uncond/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/delivery/) |
| Irreducibility of a reduced sl₂ module | [00:50:36 / 20,297,548](test_cond/lie-module-irreducibility/rigorous-proof/20261101-fresh-full-18b3e2e0bf/OWNER_FINAL_REPORT.json) | [01:40:17 / 22,583,229](test_uncond/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/delivery/) |
| Energy conservation for a sphere-valued wave map | [00:27:18 / 11,489,484](test_cond/wave-map-energy/rigorous-proof/20261101-fresh-full-18b3e2e0bf/OWNER_FINAL_REPORT.json) | [01:09:49 / 16,589,112](test_uncond/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/delivery/) |

The November 1 conditional baseline used 10 local workers per case and passed Audit B. The November 10 unconditional runs used automatic worker counts. All three passed Audit A, Audit B and the final Lean check under the original hypotheses, with zero additional premises. Each delivery directory contains the Lean proof (`formalization/Solution.lean`), the theorem statement, the audited NL0 graph and `run.json`. To check a downloaded delivery, pass its directory to [Yui’s `verify-delivery` command](https://github.com/yuiyuiui/Yui#use).

The November 10 records identify the [Yui revision used for those runs](https://github.com/yuiyuiui/Yui/commit/3e21dfc135a1bf2d6871dc55a436e7203f07ae9f). Historical logs and audit records preserve their original paths. For any retained file recorded under the former `test_uncond-test` directory, its suffix is the same under `test_uncond/`. [Earlier runs in Git history](docs/run-records-2026-11-06.md)

## Run an exercise

After [local setup](#local-setup), open a fresh Codex chat at the root of this repository. Choose one entry. Each pair uses the same problem text and complete target.

| Problem | Conditional formalization | Unconditional formalization |
| --- | --- | --- |
| Hausdorff dimension of a product with an interval | [Conditional entry](test_cond/geometry-product-dimension/README.md) | [Unconditional entry](test_uncond/geometry-product-dimension/README.md) |
| Irreducibility of a reduced sl₂ module | [Conditional entry](test_cond/lie-module-irreducibility/README.md) | [Unconditional entry](test_uncond/lie-module-irreducibility/README.md) |
| Energy conservation for a sphere-valued wave map | [Conditional entry](test_cond/wave-map-energy/README.md) | [Unconditional entry](test_uncond/wave-map-energy/README.md) |

For example, the following prompt starts one unconditional wave-map test.

```text
Execute test_uncond/wave-map-energy/README.md.
```

From another working directory, give the absolute path to that entry. Use **gpt-6.1-sol / high / Standard** for the foreground exercise or Yui benchmark chat. The [project configuration](.codex/config.toml) supplies these defaults in a trusted checkout. Each entry uses fresh source inputs, starts its own workers, reports in the owning chat every ten minutes and cleans up its temporary resources. Fresh runs size their local review and Lean proof worker pools from the node count in each phase.

## Benchmark

| Method | Elapsed time | Observed input + output tokens | Results |
| --- | ---: | ---: | --- |
| **Yui** | **04:09:26** | **282,760,473** | [Full workflow](benchmark_cond/Yui/results/20261031T212422Z-533b379994/) |
| **Pure model, including supplement** | **11:06:03** | **248,548,201** | [Pure-model results](benchmark_cond/pure-model-result/README.md) |

**In this recorded benchmark, Yui completed the task 2.67× as fast as the pure model, using 13.8% more observed tokens.** The pure-model total includes its original attempt, supplementary repair and acceptance review.

The input is the repository author's [natural-language proof](benchmark_cond/Yui/aim-518-kdv-log-loss.pdf) of [AIM problem 518: removing the logarithmic loss in the Li–Wu KdV integrator](https://github.com/MColbrook/AIM/blob/main/problems/518-kdv-integrator-logarithmic-loss.md), listed as **SOLVED** by the AIM repository following independent AI review. The benchmark compares both approaches on the paper's complete Theorem 1 and tests Yui's reliability on a larger proof.

Despite the [original prompt](benchmark_cond/pure-model-result/20261028T154300Z-b21e5d9a/prompt.md), some external theorem statements in the pure-model proof were weakened consequences of the originals. The [supplement](benchmark_cond/pure-model-result/20261101T114606Z-5d3193f6/) supplies faithful original statements, proves the missing Lean bridges and connects them to the unchanged original proof. The [completed Lean project](benchmark_cond/pure-model-result/20261101T114606Z-5d3193f6/frozen-candidate-002/) compiled and passed the recorded acceptance review. Both approaches retain the cited literature theorems as explicit inputs.

**Configuration:** all model stages requested **gpt-6.1-sol / high / Standard**, using clean background Codex CLI processes. Yui allowed **20 local workers** in this benchmark; pure-model construction used one author session per run. These are recorded workflow timings with different parallelism. Usage is `PARTIAL`; token totals count observed input plus output, with cached and reasoning tokens already included. Detailed records: [Yui](benchmark_cond/Yui/results/20261031T212422Z-533b379994/FINAL_OUTCOME.json), [pure model](benchmark_cond/pure-model-result/20261101T114606Z-5d3193f6/owner-records/accounting.json), and [Yui entry](benchmark_cond/Yui/README.md).

### Run the benchmark

The [Yui benchmark entry](benchmark_cond/Yui/README.md) uses the original paper. Its [settings](benchmark_cond/Yui/settings.json) currently select `track: nl0`, which ends after the natural-language audit. To run through Lean and Audit B as in the comparison above, set `track` to `full` before starting a fresh run, then give the owning chat this prompt.

```text
Execute benchmark_cond/Yui/README.md.
```

For the other arm, use the [pure-model reproduction instructions](benchmark_cond/pure-model-result/REPRODUCE.md) in a separate fresh chat. They cover a new evaluation, the historical supplementary repair and rebuilding the accepted proof.

## Local setup

On macOS, install the complete [Yui skill from main](https://github.com/yuiyuiui/Yui#4-installation-and-requirements), create its local Python environment and run its `doctor` check. Yui's [setup guide](https://github.com/yuiyuiui/Yui/blob/main/docs/setup.md) lists the authenticated Codex CLI, matching Code Mode helper and pinned Lean/Mathlib prerequisites. For the PDF benchmark, also install Poppler's `pdfinfo` and `pdftoppm`.

The unconditional entries in this release check for [Yui `main` at 748663fc](https://github.com/yuiyuiui/Yui/commit/748663fce1c885a7e5ff3fa528faac49d266daf5). Each entry's `settings.json` contains the full revision. Keep that checkout fixed throughout preparation and dispatch. Clone this results repository separately and open it as the working directory for the prompts above.

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

The paired `problem.md` files in the two test directories identify and quote three exercises from Stein and Shakarchi's *Real Analysis*, Humphreys' *Introduction to Lie Algebras and Representation Theory*, and Evans' *Partial Differential Equations*. Those quoted statements retain their authors' and publishers' rights. The project's own interpretations, solutions and formalizations are licensed only to the extent that contributors hold the relevant rights.

Mathlib and other dependency excerpts retain their upstream attribution and licenses; see [Mathlib's license](https://github.com/leanprover-community/mathlib4/blob/master/LICENSE). Archived Yui runtime code is original project code, but its external dependencies are not relicensed by this repository. Raw execution records can contain quoted third-party text or tool instructions; MIT covers the contributors' original portions, not those embedded materials.
