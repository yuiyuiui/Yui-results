# 测试结果

状态：`WORKFLOW-PASSED`

要求：`conditional`；题目：`wave-map-energy`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-05T08:17:08.114420+00:00",
    "terminal_at_utc": "2026-11-05T09:16:18.518976+00:00",
    "total_seconds": 3550.404556,
    "case_seconds": 3504.4400447499975,
    "closed_at_utc": "2026-11-05T09:19:56.266783+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 12095165,
      "output_tokens": 107110,
      "total_tokens": 12202275,
      "cached_input_tokens": 10969728,
      "reasoning_tokens": 22858
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-05T09:13:56.900089+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0-to-lean/preparation/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/wave-map-energy/rigorous-proof/20261105T081708Z-2a1e12241d/workflow/nl0/0001-0001/stage/usage.json"
      ],
      "missing_ledgers": []
    }
  },
  "warnings": null,
  "closure": null
}
```
