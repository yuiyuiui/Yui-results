# 测试结果

状态：`WORKFLOW-PASSED`

要求：`unconditional`；题目：`lie-module-irreducibility`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-15T13:56:44.274601+00:00",
    "terminal_at_utc": "2026-11-15T15:37:16.076258+00:00",
    "total_seconds": 6031.801657,
    "case_seconds": 5968.108251458034,
    "closed_at_utc": "2026-11-15T15:40:10.615387+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 20618283,
      "output_tokens": 204636,
      "total_tokens": 20822919,
      "cached_input_tokens": 18241024,
      "reasoning_tokens": 60572
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-15T15:35:27.786346+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/2basis/0001/stage/frontier/B101/418e67533d7234dec2b2ac5615410d5b4235588a58545705ae91cf364f88e389/attempt-dcaud7v2/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/2basis/0001/stage/frontier/B101/b42d75cad62c93566719fcdd42c6e0d65b73020202ca23d6a8a71e88c8b6def4/attempt-q7jv0_kq/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/2basis/0001/stage/frontier/B102/19c4b9e61a0b577100b97ea13424c0ab686d0b18e32300f4181c1cec67348cb3/attempt-58xqxc6l/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/2basis/0001/stage/frontier/B102/6e909f410d81752cf7ed4060d7ad76c4ec865d3dcd3323bf3ba4aed86283f095/attempt-f7f7_e4l/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/2basis/0001/stage/frontier/B103/60e0f3d323f621def333bfa38707e04a351be5146045d5589e0fea6018fd5f86/attempt-2bcgoglu/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/2basis/0001/stage/frontier/B103/63dec58f61622087938208f9edb16079d40fac3430f15a70f857402791dbc738/attempt-vx69ii0z/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/2basis/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/audit-a/local-0001-R006-0001/R006/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/audit-a/local-0001-R007-0001/R007/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/audit-a/local-0001-R008-0001/R008/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/audit-a/local-0001-R009-0001/R009/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/global-graphs/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/private-proofs/21ca85726c8101ed2738376de90c6b5c04717bc49b052ea0dc637ab0f155651e/attempt-bi11r5yh/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/private-proofs/3fe747ca48979c9ea825f27d144bff331783a949d4dc16957387b6d65e9fa085/attempt-qg0pii3v/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/private-proofs/6fa1040c7776c240d1de14cac7d06097d7cd8be8216dbcb01d63159dd8936c21/attempt-1xi2xhkl/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T010/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T011/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T012/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T013/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T014/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T015/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T016/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T017/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/nl0/local/stage/usage.json"
      ],
      "missing_ledgers": []
    }
  },
  "warnings": null,
  "closure": {
    "unconditional": true,
    "kernel_closed": true,
    "remaining_premises": [
      "H001"
    ],
    "residual_class4": [],
    "native": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/b2lean/check.json",
      "sha256": "2204ed4553a06c75feafe134d30321d402fc4a871a42126583b14f294c795570"
    },
    "proof": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261115T135645Z-fc5149ef0f/workflow/b2lean/Proof.lean",
      "sha256": "5f36f311f3c131d0d53da7d4b29bfb6916b7830402bed60cb8980fa24d51a1fc"
    },
    "export": "YuiClosed.P"
  }
}
```
