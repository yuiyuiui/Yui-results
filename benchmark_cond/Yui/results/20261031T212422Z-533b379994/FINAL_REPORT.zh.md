master，本次 benchmark 的完整 normal-policy 工作流验收通过，终态为 `WORKFLOW-PASSED`。已有绑定结果经本次运行的验证器再次只读校验；终止复核没有新增模型、Lean、probe 或证明运行。

派发至终态：2026-11-01 05:26:32 至 2026-11-01 09:35:58（Asia/Shanghai），14966.068 秒，即约 4 小时 9 分 26 秒。case 控制器自身记录 14964.750 秒。

验收状态与执行、计量状态分开：本次数学工作流通过；保留一次原生网络断流事件；tokens 与服务端身份覆盖仍不完整。不能据此声称无故障性能基准或隔离速度提升。

## 完整目标与输入

目标为原 PDF 的 Theorem 1，保留同一四项 H_tau 的固定无滤波时间半离散方法、实值/均值零约定、全部空间/流定义及在整个 H^gamma 初值球上的统一量词。原 PDF 是唯一初始数学来源；额外显式材料只是该 PDF 的校读公式转录。初始冻结目标与最终 spec 的 full_target 已逐字比较相等。

原文 SHA-256：`5d6432bf9c097991bf5d853f38e831a539b4f052f0ccf4010bba6e37b54507b6`。

```text
Theorem 1 (Logarithm-free convergence), with the standing definitions of Section 2 of the supplied paper.

Use normalized measure dx/(2*pi) on the torus \mathbb{T} = \mathbb{R}/(2*pi \mathbb{Z}). The Fourier coefficient is
\hat f(k)=(2*pi)^(-1) integral_0^(2*pi) f(x) exp(-i*k*x) dx,
and ||f||_(H^s)^2=sum_(k in Z) <k>^(2s)|\hat f(k)|^2, where <k>=(1+k^2)^(1/2).
These spaces are the completions of trigonometric polynomials in these norms; negative spaces are interpreted as distributions. The normalized L^2 norm is the s=0 norm. For mean-zero functions, the homogeneous norm uses |k|^(2s) in place of <k>^(2s). For s>=0,
||f||_(dot H^s)<=||f||_(H^s)<=2^(s/2)||f||_(dot H^s);
for s<0, 2^(s/2)||f||_(dot H^s)<=||f||_(H^s)<=||f||_(dot H^s).
Real-valued means \hat f(-k)=overline(\hat f(k)), and mean-zero means \hat f(0)=0.
All time suprema concern continuous representatives; derivative norms are essential suprema.

Let S_t=exp(-t*partial_x^3), so \widehat{S_t f}(k)=exp(i*t*k^3)\hat f(k).
Let P_0 be the mean and P=I-P_0. Let D^(-1)=partial_x^(-1) have multiplier (i*k)^(-1) for k!=0 and zero at k=0; D^(-2)=(D^(-1))^2.
The equation is
u_t+u_xxx=(1/2)partial_x(u^2),  u(0)=u_0. [Eq. (1)]
The exact solution u is the unique real, mean-zero C([0,T];H^gamma) solution obtained by smooth approximation and satisfies this equation distributionally.

For a positive integer L and tau=T/L, the fixed time-semidiscrete scheme is u^0=u_0 and
u^(n+1)=S_tau u^n+F_tau(u^n)+H_tau(u^n), 0<=n<L, [Eq. (2)]
where
F_tau(f)=(1/6)P[(S_tau D^(-1)f)^2]-(1/6)S_tau P[(D^(-1)f)^2],
H_tau(f)=(1/3)P[(S_tau D^(-1)f)D^(-1)F_tau(f)]
 +(tau/9)(S_tau D^(-1)f)P_0(f^2)
 -(1/54)[S_(tau-s)D^(-1)[(S_s D^(-1)f)^3]]_(s=0)^(s=tau)
 -(1/(27*tau))[S_(tau-s)D^(-2)[(S_(s-tau)D^(-2)F_tau(f))(S_s D^(-1)f)]]_(s=0)^(s=tau).
Each bracket [G(s)]_(s=0)^(s=tau) means G(tau)-G(0).
This is the fixed scheme of the paper's reference [1, Eq. (1.4)], without a spatial frequency cutoff.

For every T>0, every 0<gamma<=1 and every R>0, there exist C>0 and tau_0>0 depending only on T,gamma,R such that, for every real, mean-zero u_0 in H^gamma(\mathbb{T}) with ||u_0||_(H^gamma)<=R and every positive integer L with tau=T/L<=tau_0, this exact fixed scheme satisfies
max_(0<=n<=L) ||u(n*tau)-u^n||_(L^2)<=C*tau^gamma.
The same C and tau_0 apply to the entire stated initial-data ball; no spectral support bound or additional smoothness is a hypothesis.

In the source's standing notation v(t)=S_(-t)u(t) and M=1+sup_(0<=t<=T)||v(t)||_(H^gamma).
Constants C_M may vary from line to line and depend on gamma,T,M, but are uniform in n,tau and spectral support. Section 2.1 supplies M<=1+A(T,gamma,R) uniformly on the ball using the cited exact-flow results; it is not an extra hypothesis on u_0. The source uses the continuous estimates from [1, Proposition 3.4 and Lemma 7.2] and does not use the logarithmic convergence theorem as an input.
```

## 实际门禁

| 门禁 | 已有证据的只读复核结果 |
| --- | --- |
| NL0 结构 | STRUCTURE-PASSED；此项本身不是数学证明 |
| 独立 Audit A | 目标 PASS；23 个定义、6 个外部来源、12/12 个 R 节点全部通过，无未决项；有经审查的 background notes |
| 冻结前独立接口语义审查 | 最终 0002 的四项检查全部 PASS，与作者分离 |
| 局部 Lean 条件证明 | 17/17 检查通过；与最终组装分列 |
| 独立组装 | ASSEMBLY-PASSED，实际 standalone Proof.lean 内核检查通过 |
| native trust | KERNEL_INSPECTION_PASSED；完整依赖 3449 项，未截断；没有未证明的内部 axiom/opaque |
| 正常最终 B | AUDIT-B-PASSED；实际完整 E/P 类型及闭包与独立审查后的冻结权威一致 |
| 独立 B-final | 未调用；没有 valid-proof/interface-drift 例外，不能虚构额外语义复审 |

实际依赖中允许的公理为 `Classical.choice`、`Quot.sound`、`propext`。局部证明的内部依赖由最终组装消除；以下六项外部文献结论仍作为显式 Lean 前提。本次不把对文献原文的审查说成 Lean 内核证明了文献本身。

## 每项外部定理对应

| E | 作用 | 原始定位 | 独立 A / 最终接口对应 |
| --- | --- | --- | --- |
| E001 | 正则解、Galerkin 界、连续流与光滑逼近 | On the regularization mechanism for the periodic Korteweg-de Vries equation；Section 3, pp.5-6, (3.1)-(3.9), Definition 3.1; Theorems 4.2-4.3 pp.13-15, 5.1 pp.19-21, 6.3-6.4 pp.27-28 | PASS；equivalent |
| E002 | 精确流的 L2 连续依赖 | On the regularization mechanism for the periodic Korteweg-de Vries equation；Theorem 6.5, p.28, (6.22), with source solution convention (3.9) | PASS；equivalent |
| E003 | 连续三线性估计与常值输入估计 | An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below H1；Proposition 3.4, p.14, parts (1)-(2); C defined in (3.13), p.12; source norms Section 2.2 pp.6-7 | PASS；equivalent |
| E004 | 冻结输入的二次阶段估计 | An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below H1；Lemma 7.2, pp.32-34, with F^n defined in (7.2)-(7.3) | PASS；equivalent |
| E005 | Sobolev 乘积估计 | An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below H1；Section 2.4, p.8, (2.2)-(2.3) | PASS；equivalent |
| E006 | 原始无滤波更新的精确 twisted endpoint 恒等式 | An Unfiltered Low-Regularity Integrator for the KdV Equation with Solutions Below H1；(4.15)-(4.23), pp.22-24, and (5.2)-(5.4), p.25; scheme (1.4), p.4 | PASS；direct |

E001–E002 使用 Babin–Ilyin–Titi 的 arXiv:0910.1389v2（42 页）；E003–E006 使用 Li–Wu 的 50 页 FoCM-3.pdf。每项的完整假设、原始陈述、定义/符号映射、实际 primary 文件及哈希、Audit A 源审查和 Lean 全类型/对应说明保存在 [EXTERNAL_THEOREM_CORRESPONDENCE.json](EXTERNAL_THEOREM_CORRESPONDENCE.json)。P 的完整对应也在该文件中。

没有 UNVERIFIED_PRIMARY 或条件来源：最终 current_standard_receipt_valid=true，source_conditional=false，无 warn.json/warn.md。这个来源结论与下面的执行/计量限制不同。

## 时间、用量与配置

| 阶段 | 实际 stage 数 | 阶段内部时间区间并集（秒） |
| --- | ---: | ---: |
| nl0-authoring | 1 | 1336.721 |
| audit-a-global | 1 | 288.581 |
| audit-a-packet-replay | 13 | 268.828 |
| nl0-local-repair | 1 | 110.181 |
| translation-source-preparation | 1 | 30.491 |
| interface-authoring | 2 | 966.477 |
| interface-semantic-review | 2 | 663.881 |
| proof | 17 | 10233.901 |
| interface-proof-diagnosis | 2 | 104.295 |

控制器另记录：完整 proof phase 10568.541 秒，final audit build 673.595 秒，freeze 3.566 秒。组装两个原生调用分别为 144.640、144.586 秒；trust 调用为 175.138 秒，实际 receipts 中的 native timeout 均为 180 秒。组装合计 289.346 秒包含两个调用，不是单次调用越限。阶段区间可跨阶段重叠，工具时间已含在阶段时间内，不能相加重复计算。纯模型思考时间未知。

两阶段请求和 native 配置回读均为 gpt-6.1-sol / high / Standard，无回退。Standard 请求对应 transmitted service_tier=default。服务端实际 model ID、实际 reasoning effort 与实际 terminal tier 没有暴露，保留 UNVERIFIED。N=20；实际局部 R 审查峰值 12，局部 Lean 峰值 17；各串行 lane 保持串行。无总时间、token 或调用预算。

部分可观测 tokens：input 281,539,220；output 1,221,253；合计 282,760,473。cached input 276,809,088 是 input 子集；reasoning output 468,047 是 output 子集。40 个 canonical native stage ledger 已按真实 record_id 去重并与 final ledger reconciliation 匹配，共享 thread 的 baseline 没有重叠。不能把 40 条 stage delta 当成 40 个 provider response；真实 response 数、逐 response 覆盖与 owner 工作成本未知。全部先前修订及正常修复费用保留，未重置。

## 修复与故障保留

Audit A 包含 13 次局部审查，覆盖 12 个 R 节点，R006 经一次独立局部作者修复后复审。接口经历 0001、0002 两次提交与独立审查：第一次四项检查 FAIL、有两个 findings；现有作者/审查角色完成定位修正后，第二次四项 PASS。Lean 保留一个 proof round、17 个局部 worker 和两次接口实现诊断审查；没有整体重启、重采样或新增 run 续跑。

40 个阶段结果中 39 个为 NO_RECORDED_FAULT，1 个保留 FAULT：`nl0-to-lean/0001/interface/stage/result.json` 的原生服务记录 `responseStreamDisconnected`，消息为 Reconnecting... waiting for network / Connection failed: error sending request，native_will_retry=true。该角色随后完成提交；最终采用 0002 的已复核接口。Python remote_retries 合计为 0；不能把原生内部实际 retry 次数补写成已知数。原始故障、该阶段 execution_qualified=false 与成本均保留。

终止汇总时，绑定的 `yui.py metrics .` 因 phase_metrics.py:26 的 `KeyError: request_number` 退出。这是终止后的 owner 报表工具故障，未修改生产代码或绑定运行时。当前阶段时间来自现有 canonical result 时间戳的明确只读汇总；详情为 [OWNER_METRICS.json](owner-provenance/OWNER_METRICS.json) 和 [REPORTING_TOOL_LIMITATION.json](owner-provenance/REPORTING_TOOL_LIMITATION.json)。这项报告工具故障没有改写已通过的数学门禁。

## 交付与结束

[可读 NL0](owner-provenance/accepted-nl0-view/NL0.md)；[canonical NL0](nl0/merged-0001/nl0.json)；[Audit A](nl0/merged-0001/audit-a.json)；[独立接口语义审查](nl0-to-lean/0002/interface-review/review.json)；[最终 Proof.lean](nl0-to-lean/0002/workflow/audit-b/Proof.lean)；[machine Audit B](nl0-to-lean/0002/workflow/audit-b/machine-acceptance.json)。

[终止验证](owner-provenance/TERMINAL_VALIDATION.json)；[精确进程退出凭据](OWNER_PROCESS_EXIT_RECEIPT.json)；[最终机器报告](FINAL_OUTCOME.json)。

主控制器 PID=75622、case 控制器 PID=75625 的原始 OS start/PGID 与全部注册资源的退出由绑定 observe 检查确认。最终 live_owned_process_count=0，registered_groups_still_present=[]，batch children_exited=true、unconfirmed_pids=[]。没有待授权续跑。

监控 yui-benchmark-1 已由 host automation_update 实际删除（deleteStatus=deleted）；删除回执保存在 owner-provenance/heartbeat-deletion.json，并写入 OWNER_MONITOR_STATE.json 和 FINAL_OUTCOME.json。

本次只读取本运行的构造与终态材料；没有读取或比较其他 benchmark、并发三例测试或 direct-model 结果。并发运行共享主机和账户资源。

## 复核已有绑定证据的命令

以下仅检查本次已有证据，不启动模型或 Lean：

```sh
python3 -B /Users/syyui/projects/Yui-results/benchmark/results/20261031T212422Z-533b379994/runtime/nl0/scripts/nl0.py check /Users/syyui/projects/Yui-results/benchmark/results/20261031T212422Z-533b379994/nl0/merged-0001/nl0.json --spec /Users/syyui/projects/Yui-results/benchmark/results/20261031T212422Z-533b379994/nl0/merged-0001/spec.json --audit /Users/syyui/projects/Yui-results/benchmark/results/20261031T212422Z-533b379994/nl0/merged-0001/audit-a.json
python3 -B /Users/syyui/projects/Yui-results/benchmark/results/20261031T212422Z-533b379994/runtime/nl02lean/scripts/audit_b.py check /Users/syyui/projects/Yui-results/benchmark/results/20261031T212422Z-533b379994/nl0-to-lean/0002/workflow/audit-b --review /Users/syyui/projects/Yui-results/benchmark/results/20261031T212422Z-533b379994/nl0-to-lean/0002/workflow/audit-b/machine-acceptance.json
```
