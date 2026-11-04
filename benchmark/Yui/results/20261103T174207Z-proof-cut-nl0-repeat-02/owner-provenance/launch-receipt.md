# 本轮启动回执

master，本轮已实际启动并登记真实后台监控。当前观察阶段为 `nl0-authoring`，数学验收仍为 PENDING。

- 唯一运行目录：/Users/syyui/projects/Yui-results/benchmark/results/20261103T174207Z-proof-cut-nl0-repeat-02
- Track / policy：`nl0 / normal`；只执行 NL0 构造与独立 Audit A。
- 选定模型：`gpt-6.1-sol / high / Standard`，无 fallback；本轮局部 R 审查 worker 上限为 20。
- 无额外 case、stage、token 或 call 配额。共享配置中 full 的范围由本轮明确授权覆盖，共享 settings 与 .prepared 未修改。
- 冻结输入只有原始 PDF 的提取文本与本包完整 target-selection；原始第 2、3 页已渲染回读核对。157 个 runtime 文件及输入绑定已核对。
- 已归档本包公开部分、启动准备、范围覆盖与实际代码绑定；sealed 未读取、未枚举、未复制给 worker。

## 真实进程与调度

| 责任 | PID | OS start identity | PGID |
| --- | --- | --- | --- |
| 后台批次控制器 | 69525 | Wed Nov 4 01:48:24 2026 | 69525 |
| 本轮 case 控制器 | 69530 | Wed Nov 4 01:48:24 2026 | 69530 |
| 当前 native carrier | 69537 | Wed Nov 4 01:48:25 2026 | 69537 |

一次只读 observe 确认 controller_identity_matches=true，拥有进程仍在运行，尚未退出。初始观察没有 paused error 或 inspection error；这不预先保证后续服务健康。已记录用量为 PARTIAL，不能作为完整逐响应计量。

- 实际 heartbeat ID：`yui-nl0-repeat-02`，状态 ACTIVE，每 10 分钟一次。
- 实际 owner chat：`01a1a281-3e3e-78b2-a079-ea1f0dadd1de`；app 保存的调度配置已只读核实。
- 每次唤醒只观察本轮一次；阶段实质变化、故障、完成或需要处理时用中文通知，常规计数和 token 增长保持安静。
- `PAUSED_ERROR` 为非终态，保留监控并报告故障，不自行恢复。只在本轮终态报告固定且所有拥有进程与进程组确认退出后删除 heartbeat。

## 证据与边界

完整机器回执在本目录 `launch.json`。监控状态与日志保存在运行目录的 `OWNER_MONITOR_STATE.json` 与 `OWNER_MONITOR_LOG.jsonl`；启动命令、进程、调度、公开交接包、共享准备快照和披露记录保存在 `owner-provenance/`，位于测量数学输入之外。

这是操作启动回报，不是同行证明认证。原始来源无法核实时，只能按 Yui 规则交付有条件结果并保留 warn.json/warn.md。当前没有 NL0/Audit A 终态，不启动 translation preparation、接口、Lean 证明、组装或 Audit B。

上下文新鲜度与未读材料属于协议自述；原生测量阶段的实际隔离另由 Yui provenance 记录。本接收 chat 含主机自动注入的通用用户资料与历史记忆，但未将它们作为数学输入或转交测量模型。实际身份、输入哈希与监控登记有工具观察记录；不能将 SAME_VENDOR_FRESH_CONTEXT 当作跨厂商或技术强制隔离。

前台回合在保存本回执后结束，后台继续运行。
