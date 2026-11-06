# 测试结果

状态：`WORKFLOW-PASSED`

要求：`conditional`；题目：`geometry-product-dimension`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-05T08:17:18.089013+00:00",
    "terminal_at_utc": "2026-11-05T09:24:47.962147+00:00",
    "total_seconds": 4049.873134,
    "case_seconds": 3993.9283856660004,
    "closed_at_utc": "2026-11-05T09:32:09.833065+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 14216732,
      "output_tokens": 152341,
      "total_tokens": 14369073,
      "cached_input_tokens": 12725120,
      "reasoning_tokens": 37708
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-05T09:22:45.287331+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/audit-a/local-0001-R006-0001/R006/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/audit-a/local-0001-R007-0001/R007/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/audit-a/local-0001-R008-0001/R008/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T010/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T011/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T012/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T013/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T014/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T015/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T016/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T017/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T018/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0-to-lean/preparation/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_cond/geometry-product-dimension/rigorous-proof/20261105T081718Z-b092566535/workflow/nl0/0001-0001/stage/usage.json"
      ],
      "missing_ledgers": []
    }
  },
  "warnings": null,
  "closure": null
}
```
