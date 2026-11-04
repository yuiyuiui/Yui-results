---
handoff_id: 20261103T174207Z-codex-codex-INDEPENDENT-02
protocol_version: 1
from_agent: codex
to_agent: codex
to_context: FRESH
intent: INDEPENDENT
primary_target_node: t1
packet_version: 1
sealed_present: true
seal_open_condition: Both authorized benchmark repetitions are terminal with exact owned process/group exits verified and independent final reports fixed; only the coordinating owner opens the seal during reconciliation.
return_owner: rigorous-proof
budget_and_stop_rule: One fresh Yui normal NL0+Audit A run; no whole-case/stage/token/call quota; stop at the actual NL0/Audit A terminal gate, a supported blocker, or explicit user cancellation; no extra experiment.
authorization_ref: Current user instruction on 2026-11-04: 然后在该项目下发起两个task，并行的让这2个task都做benchmark的Yui版，只做NL0+Audit A部分
---

立即启动本包唯一指定的新 benchmark 运行，并为后台运行登记真实监控；用户已授权，不再请求启动确认。

## Primary Target

- Node id: t1.
- Exact statement, hypotheses, quantifier order, domain, regularity, ranges, conventions: original paper referenced in frozen/01-source.json and the complete source-bound target in frozen/02-target-selection.json. Independently verify this target against the original PDF before freezing it. Do not change its mathematical content or import an old constructed proof.
- Requested action: one cold Yui normal run, track nl0, only NL0 construction and independent Audit A.
- Reduction checkpoint, failure witness, lift-back map: not applicable; this is an operational benchmark invocation, not a peer proof-gap attack. Acceptance condition is the actual bound NL0/Audit A terminal outcome, with source and execution qualifications preserved.
- Scope lock: read installed Yui rules and this benchmark's startup files; write only this packet's return/ and the explicitly authorized new run root /Users/syyui/projects/Yui-results/benchmark/results/20261103T174207Z-proof-cut-nl0-repeat-02, plus registered isolated OS sandboxes created and reclaimed by the native Yui runtime. Do not modify installed code, prompts, branches, settings.json, .prepared, old runs or sibling runs. This outside-handoffs write exception follows the user's explicit request for fresh benchmark results and normal benchmark runtime resource creation. Do not create a worktree or change Git branches.

## Reading order

1. frozen/01-source.json
2. frozen/02-target-selection.json
3. context/01-execution.json
4. artifacts/readiness.json

这是两次相同输入、当前提示词的独立重复之一。两者接收相同中立任务，不分配不同证明路线，不读取对方进展或结果来指导工作。输出中文，称呼用户 master。

先读取 benchmark/AGENTS.md、README.md、settings.json，以及实际注册且启用的 rigorous-proof/SKILL.md。只使用该 skill 的 NL0 路径；不要引入 rigorous-proof-development、其他证明技能、旧证明或本项目历史结果作为数学材料。收到的全局记忆不能转交测量模型。

最新用户范围明确覆盖 settings.json、.prepared/task.md 中的 full 默认：只执行 --track nl0，normal，gpt-6.1-sol/high/standard，20 worker，无额外 case/stage/token/call 限额。保留共享配置文件不动。在 owner provenance 中记录这一明确范围覆盖。--output 必须为 /Users/syyui/projects/Yui-results/benchmark/results/20261103T174207Z-proof-cut-nl0-repeat-02，使用本包的完整 target-selection。停止于 NL0+Audit A，不启动 translation preparation、接口、Lean 证明、组装或 Audit B；NL0 路径自身按标准规则使用的来源工具不作额外变更。

本 benchmark 的 prepare_yui.py --verify-preparation 已由发送者核实有效；你在启动前再次只读核实。若共享准备记录意外失效，先记录具体差异，不修改共享规则或重跑整套软件测试。当前运行代码包含合法的未提交改动，按实际 frozen runtime/manifest 记录，不能仅以 Git 提交号断言同版本。不要修复或优化 workflow。

本包只释放原始 PDF、初始目标和操作配置。不得读取其他 result、旧审查、问题日志、来源缓存、父 task 或 sibling task；不得提供额外数学提示。保留 Yui 的正常检索与来源条件规则，原始来源不可核实的情况必须明确报告为条件结果。

先 prepare 新 run，核对 job.track=nl0、模型、worker 数、输入和 runtime 绑定，再 execute --detach。归档本包、启动准备、范围覆盖和配置到该 run 的 owner-provenance，置于测量数学输入之外。不得归档或解封 sealed/payload.tar.gz 到 worker 输入。

启动后核实 PID、OS start identity 与 PGID。使用 Codex app automation_update 在本 task 登记一个每 10 分钟的真实 heartbeat，把实际 ID、owner thread id、只包含本轮的 current_run_map 和初始观察保存在 OWNER_MONITOR_STATE.json。每次唤醒只做一次有界只读 yui.py observe；阶段有实质变化、故障、完成或需用户处理才用中文通知。常规计数和 token 增长保持安静。不循环轮询或 sleep，不读未完成证明，不提示 worker，不重启、恢复或替换仍运行/等待的工作。PAUSED_ERROR 非终态，保留监控与证据，报告实际故障及受支持操作，不自行恢复。

真实登记监控后，写 return/launch.json 和 return/launch-receipt.md，报告实际 run 路径、track、进程身份、监控 ID 与当前阶段，然后结束前台回合。不要一直等到数学完成才结束这个回合。

各次后续终态监控只核验本轮已有绑定产物，不新增模型或 Lean 运行。分别报告实际数学验收、来源条件、执行健康、用量完整性；缺失用量保持未知，cached/reasoning 不重复相加。保存 FINAL_OUTCOME.json、中文最终报告，记录初版和最终 N/R/S/F、初版/全局/局部阶段时间、局部 R 工作分布、修订/回退次数及原生故障。该报告只描述本轮，不读取基线或 sibling 作比较。所有拥有进程/进程组退出、无待执行授权恢复后才删除本轮 heartbeat。

## Required return schema

return/launch.json 与 launch-receipt.md：实际运行、配置、调度和身份检查；属于操作结果，不使用同行证明认证标签。持续后台工作不等于数学完成。

本轮终止后写 return/first-pass.md 和 return/receipt.md，含 Control、Target Preservation、Result、Return Contract、Disclosure Compliance、Cross-Agent Provenance 六节。列出读过/故意未读文件、实际写入路径、上面的明确写入例外及 observed/self-attested 的区别。记录实际 owner/model/profile 和新上下文来源；可记录 SAME_VENDOR_FRESH_CONTEXT 的上下文自述，但不能把它当作跨厂商或技术强制隔离。Yui native 独立阶段另按其实际 provenance 报告。保持 seal 关闭，不读取旧结论来撰写独立结果。

## Withheld material

旧运行的拥有者诊断和评估保存在 sealed/，本次构造和监控阶段不得读取或枚举。只做一次授权运行，不自动追加实验，也不自行修改构图策略。
