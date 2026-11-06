# Retained run records: November 6, 2026

These eleven previously uncommitted test runs are retained with their original
inputs, frozen runtimes, proof candidates, acceptance or cancellation records,
diagnostics and observed usage. They are historical construction evidence, not
inputs for a fresh test. A cancelled run is not an accepted proof.

Only the newest geometry run was revalidated during this publication closeout:
its existing bound Audit A, Audit B and unconditional b2lean receipts passed;
its exact process/workspace inventory was empty. The remaining statuses below
come from their retained final outcomes or terminal case results, without a new
mathematical review. Every listed run has a retained `CLEANED` record.

| Run | Recorded outcome | Final summary |
| --- | --- | --- |
| [test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535](../test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/) | `WORKFLOW-PASSED` | [FINAL_OUTCOME.json](../test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/FINAL_OUTCOME.json) |
| [test_cond/lie-module-irreducibility/rigorous-proof/20261105T071559Z-f79f8e65f9](../test_cond/lie-module-irreducibility/rigorous-proof/20261105T071559Z-f79f8e65f9/) | `WORKFLOW-PASSED` | [FINAL_OUTCOME.json](../test_cond/lie-module-irreducibility/rigorous-proof/20261105T071559Z-f79f8e65f9/FINAL_OUTCOME.json) |
| [test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d](../test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/) | `WORKFLOW-PASSED` | [FINAL_OUTCOME.json](../test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/FINAL_OUTCOME.json) |
| [test_uncond/geometry-product-dimension/rigorous-proof/20261105T120350Z-de9cce1dea](../test_uncond/geometry-product-dimension/rigorous-proof/20261105T120350Z-de9cce1dea/) | `CANCELLED` | [workflow/case-result.json](../test_uncond/geometry-product-dimension/rigorous-proof/20261105T120350Z-de9cce1dea/workflow/case-result.json) |
| [test_uncond/geometry-product-dimension/rigorous-proof/20261106T025824Z-4ac173c8d4](../test_uncond/geometry-product-dimension/rigorous-proof/20261106T025824Z-4ac173c8d4/) | `CANCELLED` | [FINAL_OUTCOME.json](../test_uncond/geometry-product-dimension/rigorous-proof/20261106T025824Z-4ac173c8d4/FINAL_OUTCOME.json) |
| [test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699](../test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/) | `CANCELLED` | [FINAL_OUTCOME.json](../test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/FINAL_OUTCOME.json) |
| [test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3](../test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/) | `WORKFLOW-PASSED` | [FINAL_OUTCOME.json](../test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/FINAL_OUTCOME.json) |
| [test_uncond/lie-module-irreducibility/rigorous-proof/20261105T120345Z-0e3fafadb3](../test_uncond/lie-module-irreducibility/rigorous-proof/20261105T120345Z-0e3fafadb3/) | `CANCELLED` | [FINAL_OUTCOME.json](../test_uncond/lie-module-irreducibility/rigorous-proof/20261105T120345Z-0e3fafadb3/FINAL_OUTCOME.json) |
| [test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e](../test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/) | `CANCELLED` | [FINAL_OUTCOME.json](../test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/FINAL_OUTCOME.json) |
| [test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef](../test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/) | `WORKFLOW-PASSED` | [FINAL_OUTCOME.json](../test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/FINAL_OUTCOME.json) |
| [test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921](../test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/) | `WORKFLOW-PASSED` | [FINAL_OUTCOME.json](../test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/FINAL_OUTCOME.json) |

## Oversized historical trace files

Two completed sl2 basis-review traces contain repeated request histories. Their
201,731,123 original bytes are published as 2,146,836 bytes of lossless XZ data.
The manifest records original and archive sizes and SHA-256 values. A streamed
round-trip check reproduced both original files exactly. Raw originals remain
locally and only their two exact paths are ignored by Git. No frozen source,
proof, receipt or raw local log was rewritten.

From this repository root, restore the original bytes after cloning before a
replay or a check that reads the raw event/tool logs:

```sh
python3 -B test_uncond/lie-module-irreducibility/rigorous-proof/20261105T120345Z-0e3fafadb3/workflow/runtime/nl0/scripts/trace_archive.py restore test_uncond/lie-module-irreducibility/rigorous-proof/20261105T120345Z-0e3fafadb3/trace-archives.json
```

The restorer verifies the archive and restored bytes and refuses to overwrite a
changed raw file. Restoring historical evidence does not resume a cancelled run.

[Archive manifest](../test_uncond/lie-module-irreducibility/rigorous-proof/20261105T120345Z-0e3fafadb3/trace-archives.json)
· [Round-trip verification](../test_uncond/lie-module-irreducibility/rigorous-proof/20261105T120345Z-0e3fafadb3/TRACE_ARCHIVE_VERIFICATION.json).
