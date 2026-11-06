# 测试结果

状态：`WORKFLOW-PASSED`

要求：`unconditional`；题目：`lie-module-irreducibility`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-06T07:18:34.827743+00:00",
    "terminal_at_utc": "2026-11-06T09:21:51.033848+00:00",
    "total_seconds": 7396.206105,
    "case_seconds": 7360.84787129199,
    "closed_at_utc": "2026-11-06T09:29:55.829830+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 14570424,
      "output_tokens": 132300,
      "total_tokens": 14702724,
      "cached_input_tokens": 13262976,
      "reasoning_tokens": 35865
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-06T09:18:35.063227+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/2basis/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/audit-a/local-0001-R006-0001/R006/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T010/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T011/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0-to-lean/preparation/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/nl0/0001-0001/stage/usage.json"
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
      "path": "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/b2lean/check.json",
      "sha256": "8e8984c97502f980f0e63ec6514aa5ee5feeff4d17126e519b59bd4c680f8cff"
    },
    "proof": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond/lie-module-irreducibility/rigorous-proof/20261106T071835Z-44ca17cbef/workflow/b2lean/Proof.lean",
      "sha256": "c865fff51e04e05feb195e4b5ebc12690724e4abaca87af31c4bd4b483413770"
    },
    "export": "YuiClosed.P"
  }
}
```
