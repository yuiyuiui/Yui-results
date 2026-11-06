# 测试结果

状态：`CANCELLED`

要求：`unconditional`；题目：`geometry-product-dimension`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-06T02:58:23.157113+00:00",
    "terminal_at_utc": "2026-11-06T07:12:11.554391+00:00",
    "total_seconds": 15228.397278,
    "case_seconds": 15191.140513541002,
    "closed_at_utc": "2026-11-06T07:13:01.077303+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 702718,
      "output_tokens": 16805,
      "total_tokens": 719523,
      "cached_input_tokens": 625408,
      "reasoning_tokens": 6266
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-06T03:07:33.928899+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261106T025824Z-4ac173c8d4/workflow/2basis/0001/stage/usage.json"
      ],
      "missing_ledgers": []
    }
  },
  "warnings": null,
  "closure": null
}
```
