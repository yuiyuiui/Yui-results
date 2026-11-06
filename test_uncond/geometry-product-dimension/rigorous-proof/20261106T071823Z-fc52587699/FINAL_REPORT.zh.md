# 测试结果

状态：`CANCELLED`

要求：`unconditional`；题目：`geometry-product-dimension`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-06T07:18:22.434193+00:00",
    "terminal_at_utc": "2026-11-06T12:54:21.775626+00:00",
    "total_seconds": 20159.341433,
    "case_seconds": 20115.918171416008,
    "closed_at_utc": "2026-11-06T12:55:16.311567+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 12339511,
      "output_tokens": 108099,
      "total_tokens": 12447610,
      "cached_input_tokens": 11287168,
      "reasoning_tokens": 23051
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-06T09:13:24.611365+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/2basis/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/audit-a/0002-0009/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/audit-a/local-0001-R006-0001/R006/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/audit-a/local-0001-R007-0001/R007/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/audit-a/local-0001-R008-0001/R008/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/nl0/0001-0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/nl0/0002-0009/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T071823Z-fc52587699/workflow/nl0/local-0001-R001-0001/stage/usage.json"
      ],
      "missing_ledgers": []
    }
  },
  "warnings": null,
  "closure": null
}
```
