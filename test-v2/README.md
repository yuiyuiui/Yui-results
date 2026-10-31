# Yui V2 three-problem tests

This directory is the fresh input set for the installed `$rigorous-proof-v2`
skill. It contains the same three original problem statements as `test/`,
byte for byte. `inputs.json` records their relative paths and SHA-256 hashes.
No prior proof, review, runtime snapshot or result was copied here.

Use the installed skill by name; do not depend on a sibling harness checkout or
an absolute developer path. At invocation, use the model profiles and worker
counts explicitly selected for that run. Start each problem with its own
`problem.md`; previous V1/V2 results are excluded from construction inputs.

The future run directories belong below each problem's `rigorous-proof-v2/`
folder and must retain distinct run identities. Preparing these files does not
start a model, proof worker, test workflow or monitoring schedule.

| Problem | Input |
| --- | --- |
| Geometry product dimension | [problem.md](geometry-product-dimension/problem.md) |
| Lie module irreducibility | [problem.md](lie-module-irreducibility/problem.md) |
| Wave map energy | [problem.md](wave-map-energy/problem.md) |
