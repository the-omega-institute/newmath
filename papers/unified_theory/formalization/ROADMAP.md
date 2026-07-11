# PZG–BEDC full-tower formalization ROADMAP

本文件是整座塔 mathlib 形式化的施工总纲:四域划分、按 ROI 排序的施工序、生态杠杆、诚实边界、当前状态。
逐条 claim 的分类见 `full_tower_gap_map.md`;`MinusWindow` 窗口界的证明骨架见 `minuswindow_scoping.md`。

## 0. 立场:形式化的极限 = 塔自己的定理 17.8

用 Lean+mathlib(一致性强度 ≈ ZFC + 可达基数级)形式化本塔,能做到**层级化、相对、模式性**的全塔形式化:
对任意层 α,`Con(T_α)` 于本层"可反驳而不可证实"可作为定理模式证出;但**绝对封顶不可得**——
这不是工程限制,是塔的定理 17.4(iv)/17.8 自身写下的内容。理论预言了自己形式化过程的形态,
这比"全部证完"是更强的自洽性检验。据此:开叶子保持 `Prop`,不假证,不粉饰。

## 1. 四域划分

- **域 A(有限/组合/代数,已证 + 可即扩)**:ch1–9 骨架、ch6 有限黄金代数、Beatty/进位组合层。全部可深度形式化,多为中低难度。
- **域 B(解析,可形式化,基础设施 2026 已备)**:完成化机器(ch23)、级联恒等式(6.11/6.14/6.19)、逐阶亚纯延拓(6.57(i))、拉回线定理(6.32)。
- **域 C(元数学塔,可形式化为相对化模式)**:ch14–17。Lean 生态已有直接对口库。
- **域 D(开放数学,只能 statement-only Prop)**:O-5 独立控制、O-6 正性、6.57(ii) 自然边界、RH 本体。形式化不生产新数学。

## 2. 2026 生态杠杆(四块地基已被打好)

- **O-9 → mathlib Loeffler–Stoll zeta**:`riemannZeta`、`riemannZeta_eulerProduct`、函数方程 `completedRiemannZeta_one_sub`/`riemannZeta_one_sub`、ζ≠0 于 Re≥1、`RiemannHypothesis` Prop 均在 mathlib,且证明路线(Poisson→Jacobi theta→Mellin)与本塔 23.9→23.10 同构。O-9 从〔closed·窗口〕升〔closed·Lean〕靠**对接**,非重写。
- **素数定理**:PNT+ 项目已在 Lean 形式化(带误差项)→ 供养 6.32(ii)。
- **Gödel I/II**:FormalizedFormalLogic/Foundation 库有 sorry-free 机器证明 → 17.8/O-2。Kleene 递归定理 `Nat.Partrec.Code.fixed_point` 在 mathlib → 16.1 / 机器公设 U 降为引用。
- **Frougny(Pisot / 有限自动机)**:φ 是 Pisot,进位归一化终止性有经典靶标 → 5.7。
- **Walnut / Fibonacci-automatic**:6.44–6.49 Beatty/Sturmian 层属可判定片段;verified Fibonacci 自动机 = 可独立发表支线。

## 3. 施工序(按 ROI)

- **P0 — 关闭 DeficitTrichotomy(进行中)**:6.25 已**机器验证地归约**到唯一 front-line 引理 `MinusWindow`
  (`deficitTrichotomy_of_window`,commit 172fb8f9a4)。地基 `betaMinusReal_eq_sum`(β₋=Σψ^i)已落(6b51676d7c)。
  剩:证 `MinusWindow` 本身。**推荐 route 甲(几何级数)**:非相邻指标 + |ψ|=1/φ,经 disjoint-shift
  `(1+r)Σ_{i∈S}r^i = Σ_{i∈S⊔(S+1)}r^i ≤ r²/(1-r)` ⟹ `Σ≤1/φ`;对称界 `|μ|<1/φ` 已足够
  (因 `3/φ<2`)。route 乙(Beatty floor 6.45)前置 Wythoff 定理且可能与 MinusWindow 循环,置后。
- **P1 — 进位终止(Frougny)**:Fibonacci 权重 + 字典序良基,接 `Rewriting.newman_confluent` ⟹ 5.7 从"典范定义"升"算法定理"。
- **P2 — 有限黄金层升格**:6.6 对角坍缩(几何级数,易)、6.35–6.36 迹映射/Cassini–Fricke(多项式恒等式 + Binet/PowerSeries,易)、6.40/6.49/6.53/6.59 Witt 封闭律(形式幂级数簿记,繁但无概念障碍)、6.46 极限分布(2D Weyl,mathlib 有无理旋转遍历性)。
- **O-9 对接**:23.6/23.9/23.10 逐条接 `completedRiemannZeta_one_sub`。
- **P3 — 解析旗舰(可发表)**:mathlib `LSeries` 内定义 λ₋/Z_qc → 6.11 ζ·H 分解 → 6.12 横标 → 6.14/6.19 级联 → **6.32 拉回线定理**(真实条件等价,最深引注 ζ|_{Re=1}≠0 已在 mathlib)。
- **P4 — 塔对接(域 C,可并行)**:16.1←`Nat.Partrec.Code.fixed_point`;16.2←Rice 对角;17.8←Foundation G2;U 降为引用。
- **P5 — 账本纪律 Lean 化身**:五态(closed/closed·窗口/tail/open/semantic)↔ Lean 证明状态(theorem/Prop/定义选择),用 namespace/attribute 制度化,使 `lake build` 成为账本审计器。

## 4. 已建(origin/feat/unified-theory-mathlib,全绿 no sorryAx)

生成层 ch1–3、编码层 ch4–7(PZG 双射 5.5/5.6)、黄金双面 ch6(PhiInt/λ±/carry/deficit 6.22/Cassini)、
读数 8.5/9.10、对角 16.2–16.3、成本 18.11–18.12;**中线代数无条件心脏**(Length/Phase:19.3/23.8/24.4/24.8
`ontic_balance_on_critical_line` 本体零点⟹Re=½ 不假设 RH);**RH 账本重述桥**(RHBridge:`rh_iff_all_projected_ontic`
= 与 mathlib `RiemannHypothesis` 的**已证等价**,开叶子 + conditional);**P0 归约**(6.25 → MinusWindow)。

## 5. 诚实边界(E3 纪律)

不能做成定理:O-5 独立控制、O-6 正性泛函、6.57(ii) 自然边界严格化、RH 本体。只能 `Prop` 入册 + 已证等价转写
(如 24.10 的 RH ⟺ 每个投影零点皆本体零点,已建)。**形式化把字典焊死,不造发动机**:P3 拉回线定理做出后,
依 E3,覆盖带条件经镜像等价于 RH 全体——不得把形式化进度误读为 O-5/O-6 进度。陈述的形式正确性本身需审计
(Loeffler–Stoll 的 ζ(1) junk-value 教训 = E6 检查器盲区同类事件)。
