# BEDC 质量测量 harness 索引

这些脚本是对抗共识(/sshx 多视角 + GPT-pro 多轮)产出的**质量测量层**:把"散文/grep 印象"换成可复跑的真信号。按信息治理纪律,本文件只存**方法 + 运行命令 + 各自回答的问题**,不缓存会过时的数字(数字一律实时从脚本读出)。全部 informational(默认 exit 0),可后续按"informational → advisory → hard gate"渐进升级。

## 两轴纪律(读任何质量数字前先记住)

BEDC 有两条**独立**的轴,任何"% done"单一数字都是 category error:
- **bedcNative 轴** = 0-axiom/0-sorry first-principles constructive 成熟度(formalstatus / theoryclosure)。
- **stdInterop 轴** = 与 Std/mathlib 传统对象的可传输等价(stdEquivChecked)。在 mathlib-free core 里结构性为 0;真外部桥需 operator-scope 的 axiom-firewalled `BEDC.StdBridge` 层(Core 不 import 它,CI 证明 Core `#print axioms` 干净)。

用户目标"导出传统数学等价对象"是 stdInterop 轴的目标;它只能挂在该轴,不能当 BEDC 总成绩。

## harness 清单

| 脚本 | 回答什么 | 运行 |
|---|---|---|
| `lean4/scripts/semantic_payload_audit.py` | 全树 conclusion-aware parameter-echo 真数(把 raw `(x:∀…hsame)` grep 噪声 ~400× 收敛到真 echo;复用 phase_d_lint 的精确谓词)+ 机械-arity 残留 | `python3 lean4/scripts/semantic_payload_audit.py` |
| `lean4/scripts/interop_axis_audit.py` | 两轴 dashboard:bedcNative(formalstatus/theoryclosure)vs stdInterop(bridgestatus + 核心里 mathlib import / stdEquiv 声明 / 真外部传输定理)+ obstruction ledger(notclaimed 里 quotient/completeness/choice/host-equality 计数) | `python3 lean4/scripts/interop_axis_audit.py` |
| `lean4/scripts/claim_inflation_audit.py` | earned-status claim gate:project-anchored 散文里"等价于 standard/traditional ℝ"(Rule A,mathlib-free core 恒未挣得)/ "axiom-clean"(Rule E)未挣得即标记;project-anchor + notclaimed/negation 豁免控 FP。`--strict` 让 ERROR exit 1(默认不开) | `python3 lean4/scripts/claim_inflation_audit.py [--strict]` |
| `lean4/scripts/reverse_replay_audit.py` + `reverse_replay_benchmark.json` | 硬传统定理的 4 态 dashboard(replayed_in_bedc / transferred_to_std / blocked_missing_carrier / blocked_forbidden_principle)+ 验证 replayed 的 Lean decl 不漂移 | `python3 lean4/scripts/reverse_replay_audit.py` |

## 怎么解读

- semantic_payload:真 echo 应接近 0(phase_d gate 合并时已拒);若 conclusion-aware 真 echo 涨且落在 mature/bridge 路径 = 质量事故。
- interop_axis:`true_external_transfer_theorems` 在 mathlib-free core 恒 0;增长要靠 operator-scope StdBridge 层,不是 core。obstruction ledger 大是**诚实**(主动 disclaim 传统等价所需原则),非缺陷。
- claim_inflation:Rule A 命中 = 真过度宣称(承诺了 stdInterop 轴没挣得的等价);近 0 = notclaimed 纪律成立。FP 复发就收紧 ANCHOR/DISCLAIMER/verb 词表。
- reverse_replay:推进目标 = 把 `blocked_missing_carrier`(可建前沿,Nat 先)变 replayed,再经 StdBridge 层变 transferred;`blocked_forbidden_principle`(Real completeness/quotient/host-equality)在 0-axiom core 永久,绝不可包装成进度。

## 战略方向(对抗共识收敛 + GPT-pro 二轮反驳存活)

1. **claim type system**:所有公开声明强制打互不蕴含的 earned-status 枚举,杜绝 mature/bridge/equiv/traditional 借光(claim_inflation gate 是其执行起点)。
2. **axiom firewall 非 budget**:Core 永远 0-axiom;StdBridge 单独层带 hostAssumptionBridge 状态,CI 证明 Core 不依赖它。
3. **冻结 KPI 晋升,不冻结探索**:生成器/横向产出进 explore/quarantine,过具体 carrier + premise-deletion/mutation 检验才进 mature/bridge KPI。
4. **obstruction-first**:早建红色 Real/quotient/completeness ledger + reverse-replay benchmark 驱动,胜过绿色 toy bridge。
