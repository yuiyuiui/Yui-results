# 测试结果

状态：`CANCELLED`

要求：`unconditional`；题目：`lie-module-irreducibility`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-06T02:58:23.178508+00:00",
    "terminal_at_utc": "2026-11-06T07:12:10.754539+00:00",
    "total_seconds": 15227.576031,
    "case_seconds": 15195.901686833007,
    "closed_at_utc": "2026-11-06T07:12:58.823372+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 18521170,
      "output_tokens": 160537,
      "total_tokens": 18681707,
      "cached_input_tokens": 16958976,
      "reasoning_tokens": 49961
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-06T04:10:45.096515+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/2basis/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/audit-a/local-0001-R006-0001/R006/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T010/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T011/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T012/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T013/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0-to-lean/preparation/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T025824Z-675e32283e/workflow/nl0/0001-0001/stage/usage.json"
      ],
      "missing_ledgers": []
    }
  },
  "warnings": null,
  "closure": null
}
```
