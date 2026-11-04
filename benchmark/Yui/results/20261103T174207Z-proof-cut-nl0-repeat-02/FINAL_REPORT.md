# 本轮 NL0＋Audit A 最终报告

本轮原生结果为 **DRAFT-AUDIT-PASSED**，仅覆盖 NL0 与独立 Audit A。冻结目标与原始 PDF 第 2 页定理及方案保持绑定，最终 14 个 R 的已有审查均为 PASS；既有格式 4 回执、证据绑定及完整性由冻结 runtime 的 validator 复核有效。该检查不是新的数学证明或 Lean 验证。

实际 case 耗时 **3301.05 秒（55 分 1.05 秒）**。存在两个标记 FAULT 的阶段及部分用量；本轮不构成无执行故障、完整计量的性能 benchmark。

## 范围与配置

- 运行：/Users/syyui/projects/Yui-results/benchmark/results/20261103T174207Z-proof-cut-nl0-repeat-02
- gpt-6.1-sol / high / Standard；normal；20 worker；局部审查实际峰值 14。
- 无额外 case/stage/token/call 配额。共享 full 默认由用户本轮明确 NL0+Audit A 授权覆盖，未改共享设置或 .prepared。
- 只以原始论文提取文本和本包完整目标开始；seal 未读取、未枚举。未读取其他运行或父/sibling chat，未作比较。
- 没有 translation preparation、接口、Lean 证明、组装或 Audit B；25 个阶段记录的 Lean 调用均为 0。

## 验收与来源

- target、25 个定义、5 个 E、14 个 R 的绑定审查完整；未解决审查为 0。
- 源码静态核验结果：current_standard_receipt_valid=true，independent_review_accepted=true，mathematics_automatically_verified=false。
- 5 个 E 的五项文献检查均有原生 PASS；没有 UNVERIFIED_PRIMARY 延后记录、source warning 或 warn.json/warn.md。这里报告已有 Audit A 的来源判断，并不宣称操作拥有者重新审核了这些出版物。

| E | 来源及位置 | 已有来源审查 |
| --- | --- | --- |
| E001 | Anatoli V. Babin; Alexei A. Ilyin; Edriss S. Titi: On the regularization mechanism for the periodic Korteweg–de Vries equation；Section 3, pp.5–6; Theorems 4.2–4.3 pp.13–15,5.1 pp.19–21,6.3–6.5 pp.27–28 | PASS；五项均 PASS |
| E002 | Buyang Li; Yifei Wu: An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below H1；Proposition 3.4, pp.14–19; definition (3.13) p.12; norm conventions pp.6–7 | PASS；五项均 PASS |
| E003 | Buyang Li; Yifei Wu: An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below H1；Lemma 7.2 pp.32–34 and formulas (7.2)–(7.3) | PASS；五项均 PASS |
| E004 | Buyang Li; Yifei Wu: An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below H1；Equations (2.2)–(2.3), p.8 | PASS；五项均 PASS |
| E005 | Buyang Li; Yifei Wu: An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below H1；(1.4) p.4; (4.14)–(4.23) pp.22–24; (5.2) p.25; (6.1) pp.26–27 | PASS；五项均 PASS |

数学结论仍相对于显式 E 及已审查的数学背景笔记。正常修订保留自身角色历史，按精确范围继承未变审查；不能把每次修订宣称为全新上下文审查。

## 图规模与阶段时间

| 版本 | N | R | S | F |
| --- | ---: | ---: | ---: | ---: |
| 初版 | 13 | 14 | 46 | 28 |
| 第一次局部合并 | 13 | 14 | 46 | 28 |
| 全局修订后 | 13 | 14 | 46 | 30 |
| 最终 | 13 | 14 | 50 | 31 |

N 为 internal proposition 数；R 为 inference 数；S 为 argument 段数；F 为各段 produces 中局部事实总数。三个原始 H、五个 E 与一个 P 另计。

| 阶段 | 次数 | 已记录 wall_seconds 合计 |
| --- | ---: | ---: |
| NL0 初版及全局修订 | 2 | 1812.84 秒 |
| 全局 Audit A | 2 | 587.89 秒 |
| 局部 R 审查及复核 | 19 | 2348.67 秒 |
| 局部 R 作者修订 | 2 | 384.30 秒 |

初版作者单次 wall_seconds 为 1446.70 秒。局部 lane（含局部作者修订）区间并集为 815.61 秒；阶段并行，阶段 wall 合计不能当作 case 耗时。stage wall 含工具、网络和服务等待，lane 时间还含调度边界，不是纯推理时间。

## 局部 R 工作分布

| R | 审查次数 | 作者修订次数 | 审查 wall 秒 | 作者 wall 秒 | 最终 S/F | 审查序列 |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| R001 | 2 | 0 | 318.09 | 0.00 | 4/2 | PASS → PASS |
| R002 | 1 | 0 | 98.72 | 0.00 | 3/1 | PASS |
| R003 | 1 | 0 | 108.96 | 0.00 | 3/2 | PASS |
| R004 | 1 | 0 | 113.10 | 0.00 | 4/3 | PASS |
| R005 | 1 | 0 | 129.04 | 0.00 | 4/3 | PASS |
| R006 | 2 | 0 | 183.47 | 0.00 | 2/1 | PASS → PASS |
| R007 | 3 | 2 | 421.81 | 384.30 | 6/2 | FAIL → FAIL → PASS |
| R008 | 2 | 0 | 179.99 | 0.00 | 2/1 | PASS → PASS |
| R009 | 1 | 0 | 128.81 | 0.00 | 4/3 | PASS |
| R010 | 1 | 0 | 111.72 | 0.00 | 3/2 | PASS |
| R011 | 1 | 0 | 135.83 | 0.00 | 3/2 | PASS |
| R012 | 1 | 0 | 212.90 | 0.00 | 5/4 | PASS |
| R013 | 1 | 0 | 112.35 | 0.00 | 4/3 | PASS |
| R014 | 1 | 0 | 93.88 | 0.00 | 3/2 | PASS |

共 1 次返回全局/全局作者修订、2 次 R007 局部作者修订；局部实际审查 19 次，其中 2 次 R007 审查非 PASS，最终均由后续绑定版本解决。未重启原任务或追加实验。各阶段、逐 R 用量和 lane 区间均在 owner-provenance/final-statistics.json。

## 执行健康与用量

- 全局作者修订 nl0/0002-0015：原生连接错误 “Reconnecting... waiting for network”，附 “Connection failed: error sending request”；保留 native_will_retry=true 和 FAULT。
- R007 第二次局部作者修订：原生流断开与 response body decoding 错误，并有连接重试记录；Python 明确重试 1 次。
- 两个阶段合计保留 4 条 fault 记录，重复事件不能直接解释为 4 次独立网络故障。对应阶段 execution_qualified=false，未被最终完成状态抹去。所有阶段的身份与输入边界字段为已核验，独立审查回执仍通过；完成不表示执行无故障。
- 终态监控：all_terminal=true、all_process_exits_verified=true、拥有进程数 0、残留组为空。execution-status 的资源退出确认无错误，无等待执行的授权恢复。

已观察 input=19,117,681，output=175,755，total=19,293,436；cached input=17,623,168、reasoning output=42,601 是前述总量的子集，不另加。25 个声明阶段 ledger 合计与原生最终汇总匹配；每响应覆盖、完整总用量、实际 API request 数与实际服务层仍未知。原生 work request 共 26，不等同于 API 调用数。

metrics 命令在完成后的报告环节报 KeyError: request_number。原始 traceback 已保存在 owner-provenance/metrics-command-failure.json；统计由既有阶段记录和并发 ledger 重建，没有修改工具、代码或测量产物。

## 可复核产物

- 最终 graph：/Users/syyui/projects/Yui-results/benchmark/results/20261103T174207Z-proof-cut-nl0-repeat-02/nl0/merged-0002/nl0.json
- spec：/Users/syyui/projects/Yui-results/benchmark/results/20261103T174207Z-proof-cut-nl0-repeat-02/nl0/merged-0002/spec.json
- Audit A：/Users/syyui/projects/Yui-results/benchmark/results/20261103T174207Z-proof-cut-nl0-repeat-02/nl0/merged-0002/audit-a.json
- 冻结 validator 完整输出：/Users/syyui/projects/Yui-results/benchmark/results/20261103T174207Z-proof-cut-nl0-repeat-02/owner-provenance/terminal-validation-full.json
- 最终机器报告：/Users/syyui/projects/Yui-results/benchmark/results/20261103T174207Z-proof-cut-nl0-repeat-02/FINAL_OUTCOME.json
- 本报告、原生故障明细、来源覆盖、每阶段和逐 R 统计均保留。后台 heartbeat 将在本轮独立报告固定后删除。

## 交接披露

本接收 chat 是新建操作上下文；主机自动注入了通用用户资料及历史 MEMORY_SUMMARY，未作为数学输入或传递给测量模型。未读材料与写入边界是自述；PID/OS start/PGID、冻结文件绑定、原生 gate 和实际调度 ID 是工具观察。SAME_VENDOR_FRESH_CONTEXT 仅为自述，不是跨厂商或技术强制隔离。

完整 peer 协议审计留待协调拥有者：现有 handoff-verify.sh 会读取并枚举 sealed/，还要求 seal-open 时间戳，与本包“接收方始终保持 seal 关闭”冲突，因此没有执行，也未编造开封时间。六节回执已另作未开封范围的结构检查；不能称为通过完整协议 verifier。这个限制只涉及交接审计，不修改 Yui 的已有数学验收记录。
