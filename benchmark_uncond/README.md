# Unconditional Yui benchmark

The only execution entry is [Yui/README.md](Yui/README.md). In a fresh task,
request: `Execute benchmark_uncond/Yui/README.md`. It prepares the original
paper, runs full unconditional Yui, verifies final b2lean closure, reports
actual evidence and cleans owned disposable resources.

This directory has no bare-model arm. Conditional and bare-model historical
comparisons remain in `../benchmark_cond/`; do not use them as proof inputs.
