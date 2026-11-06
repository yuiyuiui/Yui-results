# 测试结果

状态：`WORKFLOW-PASSED`

要求：`unconditional`；题目：`wave-map-energy`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-05T12:03:32.210200+00:00",
    "terminal_at_utc": "2026-11-05T13:09:23.047504+00:00",
    "total_seconds": 3950.837304,
    "case_seconds": 3908.0032220409994,
    "closed_at_utc": "2026-11-05T13:12:49.945540+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 13545875,
      "output_tokens": 137016,
      "total_tokens": 13682891,
      "cached_input_tokens": 12235776,
      "reasoning_tokens": 32258
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-05T13:07:20.030599+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/2basis/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/2basis/0002/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/2basis/0002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/audit-a/local-0001-R006-0001/R006/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T010/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T011/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T012/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0-to-lean/preparation/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/nl0/0001-0001/stage/usage.json"
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
      "H002",
      "H003",
      "H004",
      "H005",
      "H006"
    ],
    "residual_class4": [],
    "native": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/b2lean/check.json",
      "sha256": "ca6bf3b45c7146a6623101a16692fe70b675bbaf06da3ec8305ccbce9da25a89"
    },
    "proof": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261105T120332Z-cc987d3921/workflow/b2lean/Proof.lean",
      "sha256": "1f4eec788e38e7504d967275ee9febd9aa0aa43db74605764695d659d60cfcae"
    },
    "export": "YuiClosed.P"
  }
}
```
