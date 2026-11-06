# 测试结果

状态：`CANCELLED`

要求：`unconditional`；题目：`lie-module-irreducibility`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-05T12:03:44.311068+00:00",
    "terminal_at_utc": "2026-11-05T14:25:49.816110+00:00",
    "total_seconds": 8525.505042,
    "case_seconds": 8495.527222207998,
    "closed_at_utc": "2026-11-05T14:29:13.566108+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 88177819,
      "output_tokens": 110017,
      "total_tokens": 88287836,
      "cached_input_tokens": 87924096,
      "reasoning_tokens": 63920
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-05T14:25:47.508466+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261105T120345Z-0e3fafadb3/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261105T120345Z-0e3fafadb3/workflow/2basis/0001/stage/usage.json"
      ],
      "missing_ledgers": []
    }
  },
  "warnings": null,
  "closure": null
}
```
