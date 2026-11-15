# 测试结果

状态：`WORKFLOW-PASSED`

要求：`unconditional`；题目：`wave-map-energy`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-15T13:55:28.936381+00:00",
    "terminal_at_utc": "2026-11-15T15:47:18.944812+00:00",
    "total_seconds": 6710.008431,
    "case_seconds": 6670.552024832927,
    "closed_at_utc": "2026-11-15T15:48:49.862240+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 22640065,
      "output_tokens": 226995,
      "total_tokens": 22867060,
      "cached_input_tokens": 20214656,
      "reasoning_tokens": 60275
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-15T15:43:51.569938+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/0e1a5eba82f2ed4dd7c238cd027369522cae8abf8b6ae8a802b718721a7c6955/attempt-u1mqc6mh/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/0f1e198e946ec928efe17984ba30515b73c4b0b3f5c2a60e33496d6b06a2ea1f/attempt-k_4bv6wn/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/1273fdb34aba630bd34645d31614efcfd41d4cb01a0c5b7e7f46b5f333ab7fb5/attempt-jd1pmsw8/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/172e7744a432b03d5c41087d78e73f1f7115782941e2d8e08ff69154016ec505/attempt-xu6q9m0u/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/1c79cc06c7419147a7914cbbb6318b6c52ea130c28041c0881edac009676a885/attempt-hrrynl6l/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/1f2500211d28a1751950d534b971eb7f9be46b28c0710ccb52e924af6d5af4a6/attempt-phjk0shb/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/3c96bbcb326ac94e3cfea75e30586453efc133e09878579a2c9c3c66b8a62a67/attempt-q7ajat1e/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/40610667d0f55cdf8b6a9d4883e98c97b3a2c9eec59e0a5860832057582aca42/attempt-1ngn9ipa/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/508d4dc1d49696bc68efc1d830cf85bf4a7aeac7fe746b1d42770a3ddcbc9c4b/attempt-33iq42ku/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/66224419da0a85eff17a0c78b79ebd096622e810ce10141794faa452f4981b84/attempt-7da4kvxg/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/738e8008f0564aab90010795ca07373123fae328ce51e020aa06106b90afe02f/attempt-dtlkcij3/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/758d0eddb56f3918c8d6b41826e900b649ea222505af03a955879248c732a81d/attempt-omf_q7tf/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/7b6e0be80e9b8c1d1b01037d7ce7fa2e295d476968ef268acb8474149985d632/attempt-sl_yo_bs/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/9b6633879b5024ceb7f688da35692ad3220825af859e20a08ac542c3b0d8b1ca/attempt-cahpi9gm/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/a4a586e7c332ef753cba20a44221fcf481e9285a8bb29cefd90ded2a15076e8e/attempt-7r5u072g/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/a79379abb76e9d37e3f8374bfaae12679ae2c07d836ca7e757bea87be568d820/attempt-7cufuy_d/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/c20e6ef0caa6c4e20480358bd677b8acd92d0206abaabb3a4d5cf5c0870d192c/attempt-gaqpx1gn/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/c5ecf6c440a58060ebb735b45d8abbb766b0a88cb1dbbe1826e4eb56d2b6837b/attempt-fkrgdmbc/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/foundation-proofs/e112351407e64dc13b408b9bd5495d4aef13e1dffff80c2ef744913ea7b0eec5/attempt-340ek8vq/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/frontier/B001/15826c7d57987a030b153e575b9b7a7389fcbef469cb8aaf5746e5e2126a10b1/attempt-dc5m1v7g/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/frontier/B001/52b1cd97b8f31e916ed3b817eb7c949e657a441e2c19711bc97e07a7f63a9746/attempt-ajstegjx/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/frontier/B001/f91ebeca8b7df460dcbebc17df6bbfd3351e023f82336c686038fb97c1b9c5bf/attempt-ljoajof4/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/frontier/B002/8d77f70cc3a8d632f52a1374d549662e4f86d1bc8d1ae4739850e02f40706b2c/attempt-o0c0mdv3/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/frontier/B002/d6ec4a850e55c0410487703218c3a18b203f58dbbf048caf80d8f670fd571402/attempt-brfervar/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/frontier/B002/d7e4eb02f6462d67bcf86b2182d62ed1fc7aae869e5e470d08ddb8f0e5ef4786/attempt-v55v59d4/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/frontier/B003/3b5f637d2403c19396785eb898671d5f8dce28dc5b4f67631895b8f339cf7f6f/attempt-a8byhivg/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/frontier/B003/a6fc08736ca2077ad442df3d0fa6f9126eb68f11d2636c723d5da35764875fa6/attempt-t3tg2hl8/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/frontier/B003/d37f3251ba9ce0dfaa6c20515a07ba6c0c682de1f304426f15737de3389c51aa/attempt-5hbnr_kv/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/2basis/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/global-graphs/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T010/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T011/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T012/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T013/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T014/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T015/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/nl0/local/stage/usage.json"
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
      "path": "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/b2lean/check.json",
      "sha256": "df9bd5c73038c3b9838cd37d6b2783244772074978e800a232369ae3bf219d54"
    },
    "proof": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond/wave-map-energy/rigorous-proof/20261115T135530Z-b487492a09/workflow/b2lean/Proof.lean",
      "sha256": "5351d2d4c4d2a46490a0366c57a88250dc6cdf404a627f8c18086dfe140ae120"
    },
    "export": "YuiClosed.P"
  }
}
```
