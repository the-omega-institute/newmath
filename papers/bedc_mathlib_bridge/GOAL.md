# bedc_mathlib_bridge 目标成果 (SSOT)

本文件是本子项目"目标成果 / 成功定义"的唯一真实源。事实状态(已建对象、axiom 报告)以 Lean 源码 + matrix + CI 实时为准, 本文件只定目标与边界, 不缓存数字。

## 一句话目标
交付一个**固定 mathlib 版本上、CI 锁定的有界外部校准证书包**: 一张 compatibility matrix + 一族针对**预先冻结 anchor 集**的 adequacy 定理。每行标注 `BEDC对象 | mathlib目标 | tier | 保结构定理 | 可反射性质 | 精确 axiom footprint | 信息层级`。

**成功不在于桥了多少对象, 而在于让最容易被质疑的 BEDC 名词在 Lean 里接受外部校准, 且不藏任何 classical cost。**

## 用途与受众 (决定目标该多大)
主目标是**对外可信度 + 防 BEDC 定义自欺跑偏**。受众: 外部审稿人(回答"这个 MetricSpace 是不是自造同名玩具")、BEDC 作者自己(anti-self-deception, 抓定义太弱/方向写反/漏 law)、Lean/mathlib 读者(看 theorem + axiom report 而非叙述)、构造主义/数学哲学读者(constructive 重构与经典数学的真实关系)。

**复用 mathlib 定理只是 side effect, 绝不设为主目标** —— 否则膨胀成无止境 adapter library, 反噬 BEDC 的 mathlib-free 卖点。

## 对象四分 (做 / 不做切分原则)
- **Constructive formal tier**: finite/inductive/decidable、canonical 对应、不需 choice/quotient/propext。验证 = `≃`/`↔`/结构同构 + 运算&律 preservation/reflection, **必须 0-axiom**(CI forbidden-axiom gate)。
- **Classical formal tier**: mathlib 侧天然经 quotient/Real/choice/universal property。验证 = 结构同构 / universal-property 比较, **显式列 Classical.choice/Quot.sound/propext 等代价**, 隔离在 Classical 命名空间, **绝不回灌 BEDC core**。
- **Informal correspondence tier**: 无单一 canonical mathlib target 或形式化成本远超收益。只给论文 marker + not-claimed, **不冒充 formal theorem**。
- **Out-of-scope**: 全库 API parity / 自动 theorem transfer / 反向 dependency / 证 definitional equality / 为桥改 BEDC 定义。**明确不做**, 写进 README/论文。

切分原则: 能以 canonical equivalence/iso + 结构 preservation/reflection 证明且 axiom footprint 可控 → formal tier; 只靠名字相似/实例有限/需大规模非 canonical 选择 → 至多 informal; 会导致追 mathlib API → out-of-scope。

## 行的信息层级 (headline 纪律)
- **canary**: 如 BMark≃Bool。只证明工具链/CI/matrix 正常, **不是学术成果, 不当 headline**。
- **adequacy**: 运算/律/谓词都保真, 能抓出定义跑偏(如 BEDC metric 少 separation → 只能桥到 PseudoMetricSpace, 这是**有价值的发现**而非失败)。
- **gap (最高价值)**: 度量 constructive→classical 的公理代价(反向 map 何处需 choice、equality 何处需 quotient/propext)。**这是值得写进论文的核心。**

matrix 每行须标信息层级; headline 只能来自 adequacy + gap。

## 里程碑
- **M1 基建**: 单向依赖(bridge→{BEDC,mathlib}, BEDC 永不反向) + Core/Adapter/Constructive/Classical/Audit 分目录 + 每定理 axiom footprint + CI forbidden-axiom gate + no-back-edge 守护 + matrix 半自动生成。任何人 checkout 固定 commit 可复现 matrix 与 axiom 报告。
- **M2 constructive anchor pack**: 覆盖主论文所有基础 finite/inductive 对象, 每行含运算&律保持、全 0-axiom。候选: BMark≃Bool(canary)、BHist↔List Bool、ProbeBundle α↔List α、Ext/Cont↔List 运算、有限代数/序/有限 category fragment。
- **M3 classical gap pack**: ≥3 个高信息量 gap 行, 每行写清正/反向 map 与精确 axiom 代价。候选: BEDC Cauchy completion↔mathlib completion/ℝ、metric structure↔mathlib metric/pseudo-metric、finite certified category fragment↔mathlib category/preadditive/abelian fragment。
- **M4 freeze/release**: anchor 集冻结; 每个主论文核心名都有状态(formal-constructive / formal-classical / informal / out-of-scope); 绑定具体 Lean+mathlib commit; 主论文只引 matrix 快照。

## 完成判定
预先声明的 anchor 集**全部有状态**、constructive 行全过 0-axiom gate、classical 行有 axiom ledger、informal 行有 rationale、可复现。**之后只是 versioned maintenance, 不再追 mathlib。** 规模居中: ~10–20 constructive 行 + 3–5 classical gap 行(可先冻 ~6–10 行起步)。

**完成 ≠ 追上 mathlib 所有相关对象。**

## 与主 BEDC 论文关系
papers/bedc_mathlib_bridge 作为独立 sidecar 子论文 + 形式化工程; papers/bedc 主论文只放短 section + matrix 快照与 cross-reference, 不复制对象状态/axiom 数字。独立子论文的门槛: ≥2–3 个非平凡 gap case(仅 BMark≃Bool + 几个 finite wrapper 不够)。

## 失败红线 (写进 README/论文)
1. constructive 行出现 forbidden axiom。
2. 声称"结构对应"但只证了 carrier 双射。
3. 主论文核心对象没有任一行(formal/classical/informal/out-of-scope)。
4. bridge 反向污染 BEDC import graph。
5. classical 行被当作 BEDC 的 constructive 背书(axiom laundering)。

## 当前状态
M1 大半就位 + M2 第一行(canary)已落: `BMark ≃ Bool` constructive 实例 0-axiom; RelEquiv 契约 + Mathlib adapter 解耦; 0-axiom 回归 gate + no-back-edge 守护(扫 lean4/BEDC/** 与 BEDC.lean, CI 触发含 lean4/**) + bridge CI。下一步: M2 扩 BHist↔List Bool 等 adequacy 行。
