# Yui test and benchmark results

This repository contains conditional and unconditional Lean formalizations of three mathematical exercises as tests, a benchmark comparing [Yui](https://github.com/yuiyuiui/Yui) with a pure model, and records of research formalization cases.

## Tests results

| Problem | Conditional · time / tokens | Unconditional · time / tokens |
| --- | ---: | ---: |
| Hausdorff dimension of a product with an interval | [00:30:54 / 15,080,248](test_cond/geometry-product-dimension/rigorous-proof/20261101-fresh-full-18b3e2e0bf/OWNER_FINAL_REPORT.json) | [01:49:21 / 27,875,372](test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/delivery/) |
| Irreducibility of a reduced sl₂ module | [00:50:36 / 20,297,548](test_cond/lie-module-irreducibility/rigorous-proof/20261101-fresh-full-18b3e2e0bf/OWNER_FINAL_REPORT.json) | [01:39:27 / 20,822,919](test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/delivery/) |
| Energy conservation for a sphere-valued wave map | [00:27:18 / 11,489,484](test_cond/wave-map-energy/rigorous-proof/20261101-fresh-full-18b3e2e0bf/OWNER_FINAL_REPORT.json) | [01:51:08 / 22,867,060](test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/delivery/) |

## Real cases

1. **Local smoothing, Theorem 1.2 (critical annular estimate)** — unconditional Lean formalization. [Case record](case/critical-annular-estimate.md) · [Formalization repository](https://github.com/yuiyuiui/critical-annular-estimate-lean).

## Benchmark

This benchmark compares Yui with a pure model to demonstrate Yui's speedup in **conditional Lean formalization**. Both formalize the complete Theorem 1 of [Removing the logarithmic loss in the Li–Wu KdV integrator](benchmark_cond/Yui/aim-518-kdv-log-loss.pdf) ([AIM problem 518](https://github.com/MColbrook/AIM/blob/main/problems/518-kdv-integrator-logarithmic-loss.md)).

| Method | Time | Observed tokens | Results |
| --- | ---: | ---: | --- |
| **Yui** | **04:09:26** | **282,760,473** | [Yui results](benchmark_cond/Yui/results/20261031T212422Z-533b379994/) |
| **Pure model** | **11:06:03** | **248,548,201** | [Pure model results](benchmark_cond/pure-model-result/README.md) |

**Yui completed conditional formalization 2.67× as fast as the pure model, using 13.8% more observed tokens.**

Both used **gpt-6.1-sol / high / Standard**: Yui with up to 20 workers, pure model with one author. The pure model total includes its [supplementary repair](benchmark_cond/pure-model-result/20261101T114606Z-5d3193f6/).

## Run a test

Complete [Yui setup](https://github.com/yuiyuiui/Yui/blob/main/setup/README.md), then open this repository in Codex with **gpt-6.1-sol / high / Standard**. Ask Codex to execute the selected test README.

| Problem | Conditional test | Unconditional test |
| --- | --- | --- |
| Hausdorff dimension of a product with an interval | [test_cond](test_cond/geometry-product-dimension/README.md) | [test_uncond](test_uncond/geometry-product-dimension/README.md) |
| Irreducibility of a reduced sl₂ module | [test_cond](test_cond/lie-module-irreducibility/README.md) | [test_uncond](test_uncond/lie-module-irreducibility/README.md) |
| Energy conservation for a sphere-valued wave map | [test_cond](test_cond/wave-map-energy/README.md) | [test_uncond](test_uncond/wave-map-energy/README.md) |

For example:

```text
Execute test_uncond/wave-map-energy/README.md.
```

## Run the benchmark

Ask Codex to execute [the Yui benchmark README](benchmark_cond/Yui/README.md). For the pure model, follow [its benchmark instructions](benchmark_cond/pure-model-result/REPRODUCE.md).

## License

[MIT](LICENSE). [Third-party notices](THIRD_PARTY_NOTICES.md).
