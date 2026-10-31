# Fresh three-problem Yui V2 round: final report

All three cases passed their existing full-workflow acceptance gates and the owner validated their bound artifacts without another model or Lean attempt.

Source commit: `db29c73c1d67704d98524844c5945da763507b3e`. Both profiles: `gpt-6.1-sol`, high, Standard, no fallback. N=5 per case in separate local R-review/repair and Lean-proof phases. No total budget; native Lean single-call limit remains 300 seconds.

| Case | Actual complete Audit A | Local bodies | Assembly / kernel | Final acceptance | Case wall time |
|---|---|---:|---|---|---:|
| geometry-product-dimension | Valid current-standard receipt | 21/21 | Passed / passed | WORKFLOW-PASSED; AUDIT-B-PASSED | 36.74 min |
| lie-module-irreducibility | Valid current-standard receipt | 16/16 | Passed / passed | WORKFLOW-PASSED; AUDIT-B-PASSED | 57.58 min |
| wave-map-energy | Valid current-standard receipt | 14/14 | Passed / passed | WORKFLOW-PASSED; AUDIT-B-PASSED | 33.19 min |

Structural submission, complete actual Audit A, local-body checks, complete assembly/kernel closure and final acceptance are separate gates; each required gate is supported here. Normal final Audit B inherits the independent pre-freeze semantic review and calls no new final semantic model. No source or freeze-deviation warnings were found.

All exact owned processes and groups were verified exited in the final bounded observation. No pending pause is present. All scientific results are retained.

Usage remains PARTIAL: 38,874,791 observed total tokens, including 34,394,112 cached-input tokens as a subset. Request/response counts, unexposed actual service tier/routing and owner costs remain unknown. Per-case times overlap; no speedup or fault-free benchmark conclusion is drawn.

## Evidence and reproduction

Read-only owner observation command:

```sh
/opt/homebrew/opt/python@3.13/bin/python3.13 -B /Users/syyui/projects/Yui-v2/nl0/scripts/yui.py observe /Users/syyui/projects/Yui-results/test-v2/geometry-product-dimension/rigorous-proof-v2/20261030T202023Z-c8d1f4162b /Users/syyui/projects/Yui-results/test-v2/lie-module-irreducibility/rigorous-proof-v2/20261030T202023Z-a6f5e152d8 /Users/syyui/projects/Yui-results/test-v2/wave-map-energy/rigorous-proof-v2/20261030T202024Z-cf5e80f1ae
```

Existing final receipt validator, run with the selected run runtime on Python import paths: `final_acceptance.validate_receipt(RUN / "nl0-to-lean/0001/workflow/audit-b/machine-acceptance.json")`. It starts no model or Lean process.

- geometry-product-dimension: [case result](/Users/syyui/projects/Yui-results/test-v2/geometry-product-dimension/rigorous-proof-v2/20261030T202023Z-c8d1f4162b/case-result.json), [owner validation](/Users/syyui/projects/Yui-results/test-v2/geometry-product-dimension/rigorous-proof-v2/20261030T202023Z-c8d1f4162b/OWNER_COMPLETION_VALIDATION.json), [complete final Lean artifact](/Users/syyui/projects/Yui-results/test-v2/geometry-product-dimension/rigorous-proof-v2/20261030T202023Z-c8d1f4162b/nl0-to-lean/0001/workflow/audit-b/Proof.lean).
- lie-module-irreducibility: [case result](/Users/syyui/projects/Yui-results/test-v2/lie-module-irreducibility/rigorous-proof-v2/20261030T202023Z-a6f5e152d8/case-result.json), [owner validation](/Users/syyui/projects/Yui-results/test-v2/lie-module-irreducibility/rigorous-proof-v2/20261030T202023Z-a6f5e152d8/OWNER_COMPLETION_VALIDATION.json), [complete final Lean artifact](/Users/syyui/projects/Yui-results/test-v2/lie-module-irreducibility/rigorous-proof-v2/20261030T202023Z-a6f5e152d8/nl0-to-lean/0001/workflow/audit-b/Proof.lean).
- wave-map-energy: [case result](/Users/syyui/projects/Yui-results/test-v2/wave-map-energy/rigorous-proof-v2/20261030T202024Z-cf5e80f1ae/case-result.json), [owner validation](/Users/syyui/projects/Yui-results/test-v2/wave-map-energy/rigorous-proof-v2/20261030T202024Z-cf5e80f1ae/OWNER_COMPLETION_VALIDATION.json), [complete final Lean artifact](/Users/syyui/projects/Yui-results/test-v2/wave-map-energy/rigorous-proof-v2/20261030T202024Z-cf5e80f1ae/nl0-to-lean/0001/workflow/audit-b/Proof.lean).

The JSON companion preserves exact targets, source authorities, profiles, timings, observed usage and the final process observation. The completed heartbeat was deleted by its actual ID `yui-v2`; its successful deletion receipt is saved in owner monitor metadata.
