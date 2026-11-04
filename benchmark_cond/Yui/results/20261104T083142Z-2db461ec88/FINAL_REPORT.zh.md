# Yui 基准运行最终报告

本次结果为 **DRAFT-AUDIT-PASSED**，验收范围为 **NL0 与独立 Audit A**，覆盖原论文完整 Theorem 1。绑定证据复核成功，没有条件来源警告。执行日志保留了两处网络重连故障，且用量仅部分可见，因此本次不能作为完全无故障、计量完整的性能基准。

本报告整理本次已结束运行的既有证据。未重新调用证明模型、Lean 或探针，也未启动第二次实验。

## 数学验收与证据

- [FINAL_OUTCOME.json](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/FINAL_OUTCOME.json)：标准 Audit A 回执有效，独立审查已接受，未解决审查项为空；acceptance_target_satisfied=true、workflow_completed=true、accepted_with_warning=false。
- [最终检查报告](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/workflow/audit-a/final-0001/inspection.json)：current_standard_receipt_valid=true、full_acceptance=true，mathematics_automatically_verified=false。这表示 Yui 的自然语言审查验收，不能据此声称机器自动证明、Lean 形式化或人类同行评审完成。
- [最终全局验收](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/workflow/audit-a/final-0001/global-acceptance.json)：accepted=true、conditional=false、complete=true。
- [合并后的 Audit A](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/workflow/nl0/merged-0001/audit-a.json)：完整目标与图结构均为 PASS；30 项定义、4 项外部输入及各自 5 项引用检查全部 PASS；12 个 R 节点各自 5 项局部检查全部 PASS。
- [最终 NL0](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/workflow/nl0/merged-0001/nl0.json)与[最终规格](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/workflow/nl0/merged-0001/spec.json)共同保存接受的自然语言证明。验收包含 40 条经审查背景说明，采用 mathematical-background-v2-1，没有将背景说明改列为未经证明的原始假设。

本次轨道是 nl0。未运行接口冻结、Lean、Audit B，终态记录中的 audit_b=NOT_AVAILABLE 与该配置一致。全部已登记阶段的 Lean 调用数为 0。

## 输入、版本与前置检查

原论文 15 页全部渲染并逐页核对，原始提取与图片保持不变。完整论文转录、目标陈述和逐页修正记录在[checked-source.md](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/preparation/checked-source.md)、[target-statement.md](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/preparation/target-statement.md)、[source-review.json](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/preparation/source-review.json)。原始图形仍保存在 PDF 与页面图片中；没有从图中推造数值。来源读回属于 owner 的转录核对声明，数学内容另由 Audit A 检查。

启动前合成软件测试共 65 项：63 项通过、2 项需要安装环境的测试跳过；随后对实际注册安装单独运行这 2 项兼容测试，全部通过。阶段 1 的前置检查不计入下表从 begin 开始的计时。

| 项目 | 本次值 |
| --- | --- |
| 模型 / 推理 / 速度请求 | gpt-6.1-sol / high / Standard，无自动替代 |
| 局部审查工作槽上限 | 20，实际并发峰值 12 |
| 总预算 | case、stage、token、model-call 均未设置上限 |
| 注册安装 | /Users/syyui/projects/Yui |
| 实际运行源码版本 | adf65d18c810ffa9105e03a4b89b2fb5ad441e26，分支 proof-cut，dirty=true |
| 冻结运行时 | 154 个文件，SHA256 cb87f67208f1c0a176c8459bae6d7df93359127553b9b1ef5dea7214f88cda11 |
| 原始 PDF SHA256 | 5d6432bf9c097991bf5d853f38e831a539b4f052f0ccf4010bba6e37b54507b6 |

源码提交号不能单独代表本次含未提交改动的安装；保留的冻结运行时摘要及实际文件绑定本次执行版本。未把其他运行、旧转录或旧证明作为本次构造输入。

## 来源状态

最终绑定验证与检查报告的 source_warnings=[]、unresolved_reviews=[]，current_conditional_receipt_valid=false，没有尚待完成的 primary-source deferral。4 项 E 输入分别覆盖 Babin–Ilyin–Titi 精确流结果、Li–Wu 连续三线性估计、乘积与阶段估计，以及指定更新与余项恒等式；全局审查已检查来源与适用语境，局部应用另由对应 R 审查。

这说明本次没有条件来源资格。来源获取成功本身不是定理正确性证明，本次既有审查也未被重新包装成一次新的独立认证。

## N/R 与 S/F 组织、局部修复分布

最终图含 18 个命题：H=2、E=4、内部 N=11、目标 P=1；R=12，定义 D=30，无 M 输入。每个 N 和 P 各有唯一生产者。S 是 R 内的论证步骤，F 是步骤输出的局部事实；共 **29 个 S、18 个 F**。

局部 R 首轮 10 项 PASS、2 项 FAIL；R005、R009 各由自己的修复作者修改一次，再由对应审查角色复核通过。共 14 次局部审查阶段记录、2 次局部修复作者记录；初始作者 1 次、全局审查 1 次。合计 18 条阶段记录，涉及 16 个不同原生会话；复用同一角色的修订记录不等于增加独立审查者。

| R | 输出 | S | F | 审查序列 | 审查累计秒 | 修复作者秒 |
| --- | --- | --- | --- | --- | --- | --- |
| R001 | N001 | 2 | 1 | PASS | 210.633 | 0.000 |
| R002 | N002 | 2 | 1 | PASS | 129.457 | 0.000 |
| R003 | N003 | 1 | 0 | PASS | 138.652 | 0.000 |
| R004 | N004 | 2 | 1 | PASS | 117.061 | 0.000 |
| R005 | N005 | 3 | 3 | FAIL → PASS | 477.605 | 424.614 |
| R006 | N006 | 3 | 2 | PASS | 194.247 | 0.000 |
| R007 | N007 | 1 | 0 | PASS | 227.628 | 0.000 |
| R008 | N008 | 2 | 1 | PASS | 186.025 | 0.000 |
| R009 | N009 | 4 | 3 | FAIL → PASS | 361.163 | 237.728 |
| R010 | N010 | 4 | 3 | PASS | 207.022 | 0.000 |
| R011 | N011 | 2 | 1 | PASS | 253.933 | 0.000 |
| R012 | P | 3 | 2 | PASS | 196.441 | 0.000 |

审查与修复时间读取各阶段 result.json.wall_seconds，包含工具与服务等待，不是纯模型思考时间；并行阶段不能相加后当作整体耗时。

R005 首轮指出：在 gamma=1/2 时，外部阶段估计仅允许“充分小”的损失参数，却直接使用 1/8，缺少适用性依据。修复后从允许的前提选取充分小的损失参数，并保持目标正则指数 1/8；复核 PASS。复核还保留了一处冗余算式中 eta 的排印问题，由 BG003 给出正确的局部计算，没有把该误写当作新对象或假设。见[R005 首轮](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/workflow/audit-a/local-0001-R005-0001/R005/stage/accepted.json)、[R005 复核](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/workflow/audit-a/local-0001-R005-0002/R005/stage/accepted.json)。

R009 首轮指出：调用 N008 时未在当前包内建立比较状态所需的零均值条件。修复使用显式投影比较建立合法应用，没有添加新的原始假设；复核 PASS。见[R009 首轮](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/workflow/audit-a/local-0001-R009-0001/R009/stage/accepted.json)、[R009 复核](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/workflow/audit-a/local-0001-R009-0002/R009/stage/accepted.json)。两个初始 FAIL 均保留，未替换为首轮成功记录。

## 耗时与并发

以下日期均为北京时间（Asia/Shanghai，UTC+8），2026-11-04。

| 时点 / 项目 | 记录 |
| --- | --- |
| 测量开始 | 2026-11-04 16:31:41 |
| 后台启动开始 | 2026-11-04 16:42:19 |
| 终态记录落盘 | 2026-11-04 17:49:36 |
| 适配器完成既有证据核验 | 2026-11-04 17:54:15 |
| 输入准备墙钟时间 | 638.054 秒（10 分 38.054 秒） |
| 控制器记录 case 时间 | 4034.749 秒（67 分 14.749 秒） |
| begin 至终态记录总时间 | 4675.939 秒（77 分 55.939 秒） |
| 终态至适配器核验延迟 | 278.690 秒（4 分 38.690 秒） |
| 初始 NL0 作者阶段 | 2579.206 秒（42 分 59.206 秒） |
| 全局 Audit A 阶段 | 497.450 秒（8 分 17.450 秒） |
| 首个局部审查开始至最后复核结束（含穿插修复） | 915.260 秒（15 分 15.260 秒） |
| 14 个局部审查阶段累计 | 2699.867 秒（44 分 59.867 秒） |
| 2 个局部修复作者阶段累计 | 662.343 秒（11 分 2.343 秒） |
| 全部 18 个阶段累计 | 6438.866 秒（107 分 18.866 秒） |

准备时间与 case 时间之和同总时间相差 3.136 秒，来自上述记录的计时边界差；不把观察或报告延迟并入 case。准备时间覆盖 owner 的本次论文转录核对，但这部分 provider token 用量未暴露。局部阶段并发峰值为 12，而不是配置上限 20；未知账户或后端最大并发不作推断。

## 执行健康与计量资格

终态没有待处理错误，所有登记 PID/start/PGID 对应的进程和进程组已确认退出。完整阶段记录中 **16 条 NO_RECORDED_FAULT、2 条 FAULT**：

1. [初始 NL0 作者阶段记录](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/workflow/nl0/0001-0001/stage/result.json)。
2. [R005 局部修复作者阶段记录](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/workflow/nl0/local-0001-R005-0001/stage/result.json)。

两处均记录 NATIVE_PROVIDER_ERROR、responseStreamDisconnected、Reconnecting... waiting for network / Connection failed: error sending request，并标记 native_will_retry=true。它们最终提交了接受的阶段产物；原生重连仍是实际执行故障，不能因后来继续成功而删除。Yui 控制器的 remote_retries 合计为 0、continuations 合计为 0，阶段 error_pauses 为空；这些计数不代表原生客户端未重连。

最终检查报告记录 experiment_qualified=false、measurement_complete=false、benchmark_timing_qualified=false，performance_scope=WARM_REVIEW_REUSE_NOT_COLD_BENCHMARK。其复用是本次同一 case 正常修复/合并过程中对未变审查范围的继承，先前成本仍计入本次；不能据此声称一次全程无复用、无故障的冷性能测试。校准与行为控制为 NOT_RUN，不伪造已测状态。

## 部分可见用量

| 计数 | token |
| --- | ---: |
| 输入 | 14,531,295 |
| 输出 | 149,635 |
| 输入 + 输出 | 14,680,930 |
| 其中缓存输入（已包含在输入） | 13,355,776 |
| 其中推理输出（已包含在输出） | 35,593 |

终态 stage ledger 核对为 MATCHED，18 份用量文件齐全，账本检查没有缺失项；这仍是原生会话累计差额的 **PARTIAL** 可见量。请求数、逐响应覆盖、未上报请求、owner/provider 完整用量和实际服务层级未知。缓存输入与推理输出均为子集，不能再加一次。没有据此估算完整费用或宣称相对提速。

## 关闭记录

已生成机器终态与本中文报告，保留全部初始非通过、修复、重连与部分用量证据。监控登记与最终删除结果以[OWNER_MONITOR_STATE.json](/Users/syyui/projects/Yui-results/benchmark/Yui/results/20261104T083142Z-2db461ec88/OWNER_MONITOR_STATE.json)为准，实际自动化 ID 为 yui-20261104-2db461ec88。报告保存后删除该心跳，不再启动新实验。

owner 报告生成的首次工具调用在宿主 JavaScript 解析阶段出现引号错误，未启动子进程或写入文件；修正文本引用后完成。本条仅为报告生成诊断，不归因于 Yui 的证明模型或控制器。
