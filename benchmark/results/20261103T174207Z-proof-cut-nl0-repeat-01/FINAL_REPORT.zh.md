# 本轮 NL0 + Audit A 最终报告

master，本轮 **DRAFT-AUDIT-PASSED**，已用本轮冻结 validator 核验绑定验收。验收范围仅为自然语言 NL0 与独立 Audit A，结果相对五项显式外部定理及 45 条已审查 background notes。所有拥有进程及进程组均已确认退出。

Run：`/Users/syyui/projects/Yui-results/benchmark/results/20261103T174207Z-proof-cut-nl0-repeat-01`

模型请求/本地配置：gpt-6.1-sol / high / Standard，无 fallback；20 个局部 worker 上限，实际局部 model-stage 峰值 12。Provider 实际 routing/tier 未暴露，保持 UNVERIFIED。

启动至最终状态：2026-11-04 01:49:18 至 2026-11-04 02:50:35（Asia/Shanghai），3676.742 秒。原生 case elapsed 为 3675.503 秒。

## 验收与来源

冻结 validator 返回 current_standard_receipt_valid=true、audit_receipt_valid=true、independent_review_accepted=true；12 个 R 与完整 target 均通过，未解决审查项为空。源文件及完整 target-selection 字节绑定保持一致。5 个 E 各有 5 项 citation checks，全部为 PASS，无条件来源 warn。此处报告本轮实际审查与字节核验，不重新认证外部文献证明。

未进入 translation preparation、接口、Lean 证明、组装或 Audit B；本轮所有阶段记录的 lean_calls 合计为 0。审查角色与作者分离，返修可保留自身先前 findings；恢复的全局角色有实际新 carrier 与显式 own-history，不能把每一次修订都称为全新上下文。

## 初版与终版规模

| 版本 | N | R | S | F |
| --- | ---: | ---: | ---: | ---: |
| 首个结构验收作者稿 | 11 | 12 | 43 | 30 |
| 首轮局部合并 | 11 | 12 | 45 | 32 |
| 全局修订稿 | 11 | 12 | 45 | 32 |
| 最终验收稿 | 11 | 12 | 45 | 32 |

N 仅计 internal 命题，P 单列；S 为全部 argument 段落，F 为各段 produces 的局部事实记录总数。最终另有 H=3、E=5、P=1、D=21。45 条审核补充 background notes 不混入 F。

## 阶段时间

| 阶段 | 时间跨度（秒） | 阶段记录 wall_seconds 之和（秒） |
| --- | ---: | ---: |
| 初版 NL0 | 1750.959 | 1748.801 |
| 首轮 global A | 369.392 | 365.928 |
| 首轮 local A 与局部返修 | 672.339 | 2431.230 |
| 恢复全局作者修订 | 432.280 | 429.893 |
| 第二轮 global A | 177.744 | 175.295 |
| 第二轮 local A 与局部返修 | 214.088 | 250.495 |

跨度来自现有 start/finish 时间，包含组内阶段间隔；wall_seconds 是原始阶段字段，可因并行而重叠，也不包含所有外层初始化。两列均包含工具/网络等待，不能解释为纯推理时间，不能将并行阶段相加为全程时间。

## 局部 R 工作分布

| R | S/F | 审查次数 | 局部作者次数 | 审查累计秒 | 局部作者累计秒 | 观测 total tokens |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| R001 | 5/4 | 3 | 1 | 291.117 | 410.803 | 1,700,113 |
| R002 | 3/2 | 4 | 3 | 528.935 | 245.473 | 2,156,312 |
| R003 | 4/2 | 1 | 0 | 93.623 | 0.000 | 90,078 |
| R004 | 3/2 | 1 | 0 | 98.176 | 0.000 | 123,549 |
| R005 | 4/3 | 1 | 0 | 93.733 | 0.000 | 144,431 |
| R006 | 3/2 | 1 | 0 | 133.607 | 0.000 | 133,410 |
| R007 | 3/2 | 1 | 0 | 180.327 | 0.000 | 323,205 |
| R008 | 5/4 | 1 | 0 | 152.282 | 0.000 | 309,048 |
| R009 | 3/2 | 1 | 0 | 130.234 | 0.000 | 250,291 |
| R010 | 5/4 | 1 | 0 | 130.449 | 0.000 | 191,890 |
| R011 | 4/3 | 1 | 0 | 101.904 | 0.000 | 196,003 |
| R012 | 3/2 | 1 | 0 | 91.061 | 0.000 | 151,009 |

保留 25 个实际阶段、18 个不同 native thread。17 次局部审查；4 次局部作者阶段中 3 次提交 own-R patch，1 次返回 GLOBAL_REPAIR_REQUIRED，触发 1 次全局回退、1 次全局作者修订与第二轮审查。首轮 R001、R002 存在 nonpass，其他十项首审通过；终版 12 项全部通过。初版作者有 20 个候选/check，恢复全局作者有 5 个候选/check，这些是结构候选数，不等于独立数学修订数。原始 findings 与成本均保留，无额外 cold experiment。

## 执行健康与用量限制

一次已记录原生 provider 网络错误位于 audit-a/0001-0001/global/stage/result.json：Reconnecting... waiting for network / responseStreamDisconnected / Connection failed: error sending request，native_will_retry=true。该原始 stage 的 execution_health=FAULT、execution_qualified=false 保持不变；Python controller 的 remote_retries 合计为 0，没有 PAUSED_ERROR。最终绑定验收有效不抹去这次执行故障，不能把本轮当作全程无故障 benchmark。

内置只读 yui.py metrics 命令为 VALIDATION_FAILED：phase_metrics.py 对原生 request-lifecycle 读取 request_number 时抛出 KeyError。错误原样保存在 owner-provenance/terminal-validation/metrics.json，未修改运行时。此报告从 canonical stage_history 的 25 个绑定 result/usage 与图 JSON 直接汇总，算法保存在 owner-provenance/finalize_report.py；没有以汇总替代失败命令的状态。

观测 input=18,783,880、output=198,605、total=18,982,485。cached input=17,215,616 属于 input 子集；reasoning=57,703 属于 output 子集，均不另行相加。25 个 canonical stage ledger 与 case 总计精确对齐，无 missing ledger；provider 逐响应覆盖、请求数及 actual tier 仍未知，因此 usage=PARTIAL、measurement_complete=false。Owner 操作开销不计入以上 worker 用量。

## 范围与返回

共享配置中的 full 已由本次明确授权覆盖为 nl0；安装代码、提示词、分支、settings.json 与 .prepared 均未修改。冻结 runtime 包含启动时既有未提交改动，按实际 manifest 绑定，不能只用 Git commit 判定版本。未读取父/兄弟 chat、历史或其他 run，未读取或枚举 sealed/，无运行间比较。OWNER_MONITOR_LOG.jsonl 含真实有界观察；终态观察已确认无拥有进程/进程组，无待授权恢复。heartbeat yui-nl0-01 已在最终报告和回执保存后通过 automation_update 实际删除；真实工具删除回执保存于 owner-provenance/monitor-removal.json。

详细机器结果：FINAL_OUTCOME.json；直接汇总：owner-provenance/terminal-metrics.json；完整 validator 输出：owner-provenance/terminal-validation/audit-a-check.json；终态读取声明：owner-provenance/terminal-reading-disclosure.json。

操作返回：交接包 return/first-pass.md 与 return/receipt.md；封印保持关闭。
