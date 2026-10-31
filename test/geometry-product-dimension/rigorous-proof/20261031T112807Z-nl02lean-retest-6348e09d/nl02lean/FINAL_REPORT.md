# 三题 nl02lean 复测结果

三题均通过现有绑定产物与回执复核，结果为 WORKFLOW-PASSED / AUDIT-B-PASSED。本轮复用了上一轮完整且已接受的 NL0/A，仅重新执行翻译；未导入旧 Lean 或旧接口尝试。

| 题目 | 局部 Lean 节点 | 本轮耗时 | 最终 Lean | 机器验收 |
| --- | ---: | ---: | --- | --- |
| 几何 | 14/14 | 19 分 20 秒 | [Proof.lean](/Users/syyui/projects/Yui-results/test/geometry-product-dimension/rigorous-proof/20261031T112807Z-nl02lean-retest-6348e09d/nl02lean/nl0-to-lean/0001/workflow/audit-b/Proof.lean) | [回执](/Users/syyui/projects/Yui-results/test/geometry-product-dimension/rigorous-proof/20261031T112807Z-nl02lean-retest-6348e09d/nl02lean/nl0-to-lean/0001/workflow/audit-b/machine-acceptance.json) |
| 李代数 | 19/19 | 32 分 50 秒 | [Proof.lean](/Users/syyui/projects/Yui-results/test/lie-module-irreducibility/rigorous-proof/20261031T112807Z-nl02lean-retest-7125f0eb/nl02lean/nl0-to-lean/0001/workflow/audit-b/Proof.lean) | [回执](/Users/syyui/projects/Yui-results/test/lie-module-irreducibility/rigorous-proof/20261031T112807Z-nl02lean-retest-7125f0eb/nl02lean/nl0-to-lean/0001/workflow/audit-b/machine-acceptance.json) |
| 波映射 | 10/10 | 22 分 23 秒 | [Proof.lean](/Users/syyui/projects/Yui-results/test/wave-map-energy/rigorous-proof/20261031T112807Z-nl02lean-retest-5105bb0a/nl02lean/nl0-to-lean/0001/workflow/audit-b/Proof.lean) | [回执](/Users/syyui/projects/Yui-results/test/wave-map-energy/rigorous-proof/20261031T112807Z-nl02lean-retest-5105bb0a/nl02lean/nl0-to-lean/0001/workflow/audit-b/machine-acceptance.json) |

三题均完成本轮独立接口审核、局部证明、独立文件组装、实际内核及依赖检查，最终机器 Audit B 继承冻结接口的语义审核。
没有调用最终语义模型，无接口偏离或 B-final 例外。
实际 warn.json / warn.md 均不存在。
三题源 NL0/A 均保持输入图版本，其 Audit A 是沿用的既有验收，不是本轮重新审核。

完整目标、假设、外部对应与全部回执路径保存在 [FINAL_OUTCOME.json](FINAL_OUTCOME.json)。

| 题目 | 记录的 token 总数（部分覆盖） | 记录的自动重试 | 执行故障记录 |
| --- | ---: | ---: | ---: |
| 几何 | 8406118 | 0 | 0 |
| 李代数 | 11339318 | 0 | 0 |
| 波映射 | 7798694 | 0 | 0 |

用量来自本地原生累计计数差值，覆盖仍为 PARTIAL；响应级请求数及独立响应 token 覆盖未知。缓存及 reasoning 是子集，不另行相加。Standard 是请求配置；实际服务档位未报告。上述耗时包括本轮翻译流程，不包括沿用 NL0/A 的历史耗时。三题共享主机与账号资源，不能据此作隔离速度因果结论。

本轮后台进程及其登记进程组已全部确认退出，无待执行续跑。本轮三题及报告均已完成，已通过应用工具删除监控 yui-nl02lean。

复核只读取已有绑定产物、实际审核与编译/内核证据，未新开模型、Lean 或 probe 会话。软件修改已在提交 372046341c3523a0939d19df218b02d5b0bb67eb 发布，898 项软件测试通过；本轮通过不等于所有未来调度路径均被真实数学任务触发。
