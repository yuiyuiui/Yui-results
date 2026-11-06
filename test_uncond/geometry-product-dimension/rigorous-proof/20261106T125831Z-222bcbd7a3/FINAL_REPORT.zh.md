# 测试结果

状态：`WORKFLOW-PASSED`

要求：`unconditional`；题目：`geometry-product-dimension`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-06T12:58:30.289214+00:00",
    "terminal_at_utc": "2026-11-06T14:08:33.305089+00:00",
    "total_seconds": 4203.015875,
    "case_seconds": 4175.598293332994,
    "closed_at_utc": "2026-11-06T14:18:23.550616+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 17685658,
      "output_tokens": 145388,
      "total_tokens": 17831046,
      "cached_input_tokens": 16120960,
      "reasoning_tokens": 35431
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-06T14:06:43.400278+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/2basis/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/audit-a/local-0001-R101-0001/R101/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/audit-a/local-0001-R102-0001/R102/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/audit-a/local-0001-R103-0001/R103/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/audit-a/local-0001-R104-0001/R104/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/audit-a/local-0001-R105-0001/R105/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/audit-a/local-0001-R106-0001/R106/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/audit-a/local-0001-R107-0001/R107/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T010/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T011/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T012/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T013/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/0002/workflow/proof-run/workers/T014/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0-to-lean/preparation/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/nl0/0001-0001/stage/usage.json"
      ],
      "missing_ledgers": []
    }
  },
  "warnings": null,
  "closure": {
    "unconditional": true,
    "kernel_closed": true,
    "remaining_premises": [
      "H001",
      "H002"
    ],
    "residual_class4": [],
    "native": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/b2lean/check.json",
      "sha256": "0742ec04ca775c0d6f071d632f702abda1de7cd4af94cd401ad47f77c9cf00e7"
    },
    "proof": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T125831Z-222bcbd7a3/workflow/b2lean/Proof.lean",
      "sha256": "bae42863b731200278d52fd040025257717f040fd3bf9f3cb07256bb566563a2"
    },
    "export": "YuiClosed.P"
  }
}
```
