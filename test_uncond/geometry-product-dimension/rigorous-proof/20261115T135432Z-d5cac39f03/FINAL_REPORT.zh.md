# 测试结果

状态：`WORKFLOW-PASSED`

要求：`unconditional`；题目：`geometry-product-dimension`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-15T13:54:30.952600+00:00",
    "terminal_at_utc": "2026-11-15T15:44:45.289336+00:00",
    "total_seconds": 6614.336736,
    "case_seconds": 6561.93157783302,
    "closed_at_utc": "2026-11-15T15:46:39.746757+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 27655497,
      "output_tokens": 219875,
      "total_tokens": 27875372,
      "cached_input_tokens": 25253376,
      "reasoning_tokens": 68940
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-15T15:44:09.857440+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/foundation-proofs/728f0d82f01aac16e99d470cccd62118e0eb64b7318ee6ba042dfdd0a1a69f9a/attempt-qf8hwma4/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/foundation-proofs/7c8f1e7d39109c223e5e228e882ff7fcf517e5d6ca67e3daefa12da20329bf0c/attempt-gwsg9buf/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/foundation-proofs/832a42a8f8c7b72f7b7dad113aa900bc14a16e9e9880cadc723a3ad50e1430ff/attempt-t2x5m274/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/foundation-proofs/8db8bffd7731ab98dcf73004ab7411aceec28630ea6761dda322ffc7754057d2/attempt-n9vxzr8x/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/foundation-proofs/c2673c70df0707d76188a119f9b0aca3eed2a31fd3eac8c5fa5c1321ca4fe931/attempt-6akyqu2b/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/foundation-proofs/c6454cc95dc199c846b47a40f3a152572bd5cd4ed89f7b1bc8ec87d6f7b0d615/attempt-8uamkf74/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/foundation-proofs/e6175114a5385a17fab93d4c3e04d54233d05688f527778c8de2375d5a8faebc/attempt-6qajshj6/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/foundation-proofs/ebe44aa5c664a3dcb90ad163609f768ed49fd2611cd42370892e936180981a2e/attempt-wiz05ol4/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/foundation-proofs/f77c664f37d248f1ddedad0f021b8717868d0f2d6dd3c5c3efbb58553afe38b5/attempt-cq1131s6/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/foundation-proofs/fd147631c411a267a0b03f92e7c16ca328bf5bbaea7a2c014e24bfe19f6eb0fb/attempt-bx6vrlxj/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/frontier/B010/4c5d750c0fce5444455e70f469a710dc1c62db43df15bff6e83a1d6014690da7/attempt-gy1xqesw/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/frontier/B010/6262632ab7cf607c3cb2abb2e7ff0033b1f3fb8b6515f8ec73c7377d903dd245/attempt-9jwz82_3/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/frontier/B010/a8f322dc73dd7f8e0d5b9aac44d026317518a78e8eff9e8b43560614b5a50ac1/attempt-gkn3hrb8/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/frontier/B020/11fea7e45d8c716ed191bf6daf1bf31c5d38cc20925b0eeaa54fe01e0a1f33fa/attempt-eg7l4dtj/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/frontier/B020/415a259c8d30ef46e9bb2a4f076a9a5d7714c81171ad44831fddaf826cb12a65/attempt-5u_veptt/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/frontier/B020/b272c71d5e748ab383c4ed1f9041a1b0455d004fd3122e3f7d21e5f4f1aaa83a/attempt-33yap98x/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/frontier/B030/0eaf874ee3876eab01cee42075922a4cac15a9f60e4132fa0092db985e8aa7ad/attempt-v9hdhmnx/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/frontier/B030/7e84a8bcf89bec29f98c24136582abf22922fbf921218ec3c725ed29c4717b2f/attempt-fyfevuev/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/frontier/B030/e762173055d6d0a571ec694c5dbb60f579a5473c5b20a7f0feeab678ec8d2da2/attempt-gnlqm91w/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/2basis/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/audit-a/local-0001-R006-0001/R006/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/audit-a/local-0001-R007-0001/R007/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/global-graphs/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/assembly/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T010/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/nl0/local/stage/usage.json"
      ],
      "missing_ledgers": []
    }
  },
  "warnings": null,
  "closure": {
    "unconditional": true,
    "kernel_closed": true,
    "remaining_premises": [
      "H001"
    ],
    "residual_class4": [],
    "native": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/b2lean/check.json",
      "sha256": "511d31100ca431e4ef897963b6ea7272f1b3889c06e6b89576280190d7c68a6e"
    },
    "proof": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond/geometry-product-dimension/rigorous-proof/20261115T135432Z-d5cac39f03/workflow/b2lean/Proof.lean",
      "sha256": "cb74b0f284718469c77a57ad04ae536d06410db55395168bed8414f6cf85fcbd"
    },
    "export": "YuiClosed.P"
  }
}
```
