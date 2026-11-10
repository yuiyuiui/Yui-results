# 测试结果

状态：`WORKFLOW-PASSED`

要求：`unconditional`；题目：`wave-map-energy`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-10T12:57:15.080990+00:00",
    "terminal_at_utc": "2026-11-10T14:07:41.855530+00:00",
    "total_seconds": 4226.77454,
    "case_seconds": 4190.154366374976,
    "closed_at_utc": "2026-11-10T14:10:03.750600+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 16439803,
      "output_tokens": 149309,
      "total_tokens": 16589112,
      "cached_input_tokens": 14526848,
      "reasoning_tokens": 35067
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-10T14:06:50.173517+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/2basis/0001/stage/foundation-proofs/1a81300cac4fefe313a342757718a4deefda10d8a71905b5e9adeb8dc7fb8b0e/attempt-9zs6r48p/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/2basis/0001/stage/foundation-proofs/1e982df7032faf176242963bc6fa9b818af02b4e903c7ed67db815ab40ee030e/attempt-a4s4djrq/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/2basis/0001/stage/foundation-proofs/4f2f1c84fd89dfff6a2f9785f265a406ef7cdc07a4b5ddaee4dcb2ef9fec1a6e/attempt-njj314cj/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/2basis/0001/stage/foundation-proofs/b02a089fd26417a7312f57c783254bfb81d4d6daacc260ae5e409ea3871796fa/attempt-qx245obt/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/2basis/0001/stage/foundation-proofs/d0893b9ffe7333f89aed248d512f61ed711bf14f368441d98df9ea0d728d2551/attempt-lexhyvp5/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/2basis/0001/stage/foundation-proofs/d7b359b739a779d746fb78cf23bcad18c4246aaee5d1612eec90bd0b7354b31a/attempt-1w0cu517/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/2basis/0001/stage/frontier/B001/c52fd36c53b2a295dc852eb78a8f9f37188dc68077dfdca1875d76f4cde896a7/attempt-wujq13jb/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/2basis/0001/stage/frontier/B002/6516ccae58a22dbf436fb85e27305683181b7e4d33fc6c47e8a2144ea7253c97/attempt-ua6pr90e/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/2basis/0001/stage/frontier/B003/dbda9b13353fe0203db40b9a9ce158277c9e6e4cbbb314be055002d4954a0876/attempt-mnq2rnla/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/2basis/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/audit-a/local-0001-R006-0001/R006/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/audit-a/local-0001-R007-0001/R007/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/global-graphs/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/assembly/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T010/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T011/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T012/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T013/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T014/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T015/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/nl0/local/stage/usage.json"
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
      "H005"
    ],
    "residual_class4": [],
    "native": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/b2lean/check.json",
      "sha256": "5a168b954f39a3a64b5e442fac10d1aa36a0b6378e2ff1f2332758a9a44f9583"
    },
    "proof": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond-test/wave-map-energy/rigorous-proof/20261110T125715Z-a078c5bc5f/workflow/b2lean/Proof.lean",
      "sha256": "437ddf89b7aad60940a79522de805aaea3a7a6485f8154779f955300bde2c857"
    },
    "export": "YuiClosed.P"
  }
}
```
