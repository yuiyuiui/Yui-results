# 测试结果

状态：`WORKFLOW-PASSED`

要求：`unconditional`；题目：`lie-module-irreducibility`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-10T12:57:35.344348+00:00",
    "terminal_at_utc": "2026-11-10T14:38:28.847736+00:00",
    "total_seconds": 6053.503388,
    "case_seconds": 6017.213724875008,
    "closed_at_utc": "2026-11-10T14:47:09.303857+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 22371928,
      "output_tokens": 211301,
      "total_tokens": 22583229,
      "cached_input_tokens": 19907328,
      "reasoning_tokens": 59371
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-10T14:37:37.355132+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/2basis/0001/stage/foundation-proofs/4d6f32f48721e8a3ebbbb41441368e2e7532974f9eff1b9d5db98799dfa0ba10/attempt-kn67r880/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/2basis/0001/stage/frontier/B001/25cedc650e8f1e481daf472f9c52df9242e22d0cf7cf49d2973e773fd3e2012c/attempt-pg7b8nqb/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/2basis/0001/stage/frontier/B002/9baa3d582acea68bc073559c17648085a07616c0d95482f7bd5eb6120a9ade91/attempt-r98o7bvv/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/2basis/0001/stage/frontier/B003/893f9fb2e6615602baee16143f78dd97c396349cf966c898eec610f17d3655be/attempt-w0jnl1dd/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/2basis/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/0002-0009/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0001-R006-0001/R006/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0001-R007-0001/R007/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0002-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0002-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0002-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0002-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0002-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0002-R006-0001/R006/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0002-R007-0001/R007/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/audit-a/local-0002-R008-0001/R008/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/global-graphs/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/global-graphs/0002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/assembly/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/private-proofs/650a191f36aed0daf4511dd5528a85dd2216c2bdc616c8df653ee6c88267b01e/attempt-qjwi8nph/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/private-proofs/c11dbd4226bea50cf85132a304b3dec704d1d881dbf5e9c66c4a06d7b318642a/attempt-ku35xz89/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T010/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T011/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T012/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T013/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T014/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T015/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T016/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T017/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0/local-0001-R006-0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0/local-0002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/nl0/local/stage/usage.json"
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
      "H003"
    ],
    "residual_class4": [],
    "native": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/b2lean/check.json",
      "sha256": "434a0ed8b705126324248d21ea12a80a3e79db7093b2dd26f96251705780bcdd"
    },
    "proof": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond-test/lie-module-irreducibility/rigorous-proof/20261110T125736Z-c0496dfb22/workflow/b2lean/Proof.lean",
      "sha256": "ab9f4df51dca8acc1db7b09275c9ae3808ad991377bbb3318641e5999956425c"
    },
    "export": "YuiClosed.P"
  }
}
```
