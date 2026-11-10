# 测试结果

状态：`WORKFLOW-PASSED`

要求：`unconditional`；题目：`geometry-product-dimension`。

审查与形式化范围以 FINAL_OUTCOME.json 中的实际验证为准。条件结果、来源保留意见和未完成状态不能视为无条件完成。

耗时与 token 覆盖：

```json
{
  "timing": {
    "started_at_utc": "2026-11-10T12:56:55.630870+00:00",
    "terminal_at_utc": "2026-11-10T14:06:25.370043+00:00",
    "total_seconds": 4169.739173,
    "case_seconds": 4126.762954457983,
    "closed_at_utc": "2026-11-10T14:09:56.853046+00:00"
  },
  "usage": {
    "status": "PARTIAL",
    "confirmed_tokens": {
      "input_tokens": 16957764,
      "output_tokens": 132736,
      "total_tokens": 17090500,
      "cached_input_tokens": 15305088,
      "reasoning_tokens": 33692
    },
    "requests": null,
    "requests_with_usage": null,
    "in_flight_or_unreported_requests": null,
    "errors": [],
    "accounting_source": "native_cumulative_stage_deltas",
    "usage_last_observed_at_utc": "2026-11-10T14:05:53.458311+00:00",
    "final_ledger_reconciliation": {
      "status": "MATCHED",
      "stage_usage_files": [
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/2basis/0001/review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/2basis/0001/stage/foundation-proofs/6721deaac282ad7c444f3fde46a583042636cd6fa983fab29bedddf0140bcc0d/attempt-n48q_f6e/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/2basis/0001/stage/foundation-proofs/676f15e84482be2fe5d8fc6f89aad4cb82d029ec62bfcca2577443113473f930/attempt-rqcp3jeu/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/2basis/0001/stage/foundation-proofs/b8390df15e9c882fa95c014bc67890adf95ac5834a1379fdf4f9d28a7959307b/attempt-x90zb5oq/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/2basis/0001/stage/foundation-proofs/f1295bc2bb7eff831bbb75a37215333c01f591d8c2e412f9126cc102f86c4cdb/attempt-6gxinhov/worker/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/2basis/0001/stage/frontier/B003/fb1fd27215243c14b469e58540cd23003be484b4774a896f068c39a4989cee6f/attempt-_es8qi7p/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/2basis/0001/stage/frontier/B004/2b25faf652117a72c758294286e40f1d035badfc624f4406ca7def8b73c33b1d/attempt-xbrvinpa/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/2basis/0001/stage/frontier/B005/0b1cf6ff9952a5403eb2991b5e7298de18ce4c77cdee821495edbbbaa42714cf/attempt-y1v7i59m/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/2basis/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/audit-a/0001-0001/global/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/audit-a/local-0001-R001-0001/R001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/audit-a/local-0001-R002-0001/R002/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/audit-a/local-0001-R003-0001/R003/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/audit-a/local-0001-R004-0001/R004/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/audit-a/local-0001-R005-0001/R005/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/audit-a/local-0001-R006-0001/R006/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/audit-a/local-0001-R007-0001/R007/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/global-graphs/0001/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/assembly/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/interface-review/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/interface/stage/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T001/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T002/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T003/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T004/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T005/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T006/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T007/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T008/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T009/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0-to-lean/0001/workflow/proof-run/workers/T010/usage.json",
        "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/nl0/local/stage/usage.json"
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
      "H002"
    ],
    "residual_class4": [],
    "native": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/b2lean/check.json",
      "sha256": "a6d0d319343c60f748e1f882b7222c65e8edaaf30e54d0530fae34a2ecebd461"
    },
    "proof": {
      "path": "/Users/syyui/projects/Yui-results/test_uncond-test/geometry-product-dimension/rigorous-proof/20261110T125656Z-567075d770/workflow/b2lean/Proof.lean",
      "sha256": "8820bfc96b265d10ed40408f161523953c81642a68fcbafa125cebc66a661a13"
    },
    "export": "YuiClosed.P"
  }
}
```
