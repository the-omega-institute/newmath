# BEDC Deep Reasoning Board

Purpose: drive a self-iterating BEDC paper-extension loop. Each entry below is
a target the oracle deep-reasoning loop runs to a complete result, then
appends as canonical current-state LaTeX into `papers/bedc/parts/`. The
downstream `lean4/scripts/codex_formalize.py` lane (on dev) picks up new
theorem sites by scanning the paper.

Lane edge:
- This lane never edits `lean4/`. The handshake to formalization is the
  appended LaTeX in `papers/bedc/parts/<theme>/<concept>.tex` (no marker
  macros — those are added by `codex_formalize.py` after the Lean target lands).
- New targets are auto-spawned by Stage 1.5 topic discovery and appended to
  this board with `Status: Candidate (auto-spawned)`.

Each target card carries enough context (Object, Local inputs) for the loop
to build its initial prompt without external lookups.

---

### B-631 - NewtonIteration finite-prefix restriction carrier

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | NewtonIteration finite-prefix restriction carrier |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 8/10 |

Problem:
在 NewtonIteration finite-step carrier setup 下, 若 accepted packet 记录 n+k 步 Newton recurrence, 则截取前 n 步的迭代行、函数值行与导数非零 ledger 仍构成 NewtonIterationUp carrier。

Local inputs:
- `papers/bedc/parts/concrete_instances/201_newtoniteration_namecert_construction.tex`

Rationale:
BOARD 有 Newton finite-step concatenation closure (B-621), 但缺 prefix restriction. 它是拼接闭包的对偶 prerequisite: 长迭代证书的有限前缀可独立读回为同一对象, 证明只需限制 recurrence 与 nonzero-denominator ledger, 与 concatenation 走相反方向。Landing file 安全。

---

### B-632 - Brownian path-step carrier finite-suffix restriction

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Brownian path-step carrier finite-suffix restriction |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
在 BrownianUp BHist process-packet setup 下, 若长度 n+k 的 accepted packet 给出路径步、时间步与增量 ledger, 则从第 n 步边界端点起的后 k 步 shift-restriction 仍是 BrownianUp carrier。

Local inputs:
- `papers/bedc/parts/concrete_instances/169_brownian_namecert_construction.tex`

Rationale:
BOARD 有 prefix restriction (B-627), suffix restriction 是真正不同的局部化方向: 源端点和时间 ledger 都要重置到中间边界。比 Brownian 跨段 concatenation 更安全 — 只需限制已有增量、连续性与分布 ledger, 不需要构造跨段独立性新证据。Landing file 不在 near-cap 列表。

---

### B-633 - Sheaf pullback along composite refinements is associative

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | Sheaf pullback along composite refinements is associative |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 9/10 |
| Novelty | 8/10 |

Problem:
在 Sheaf refinement exactness setup 下, 若 r:U→V 与 s:V→W 是 accepted refinements 且 σ 是 W 上的 carried section, 则 pullback_r(pullback_s(σ)) 被 section classifier 分类为 pullback_{s∘r}(σ)。

Local inputs:
- `papers/bedc/parts/concrete_instances/sheaf/04_refinement_exactness.tex`

Rationale:
BOARD 仅覆盖 identity-refinement pullback identity (B-613), 但 sheaf refinement 接口还缺 composite refinement 的 associativity / coherence 主结构定理。这是局部限制操作的 bridge 定理, 不是 carrier 字段搬运: 证明需要 refinement 组合 + pullback exactness + section classifier 三步闭合。Landing file 安全。

---

### B-634 - AffineVar zero-locus is antitone under equation inclusion

| field | value |
|---|---|
| Status | Candidate (auto-spawned) |
| Source | bedc-deep board_spawn (oracle) |
| Object | AffineVar zero-locus is antitone under equation inclusion |
| Layer | concrete_instances |
| Route | proof |
| Risk | unknown |
| Fit | 8/10 |
| Novelty | 7/10 |

Problem:
在 AffineVarUp equation-family setup 下, 若方程族 E 的每个方程都出现在 F 中且点 x 落在 F 的 zero-locus, 则 x 落在 E 的 zero-locus。

Local inputs:
- `papers/bedc/parts/concrete_instances/132_affinevar_namecert_construction.tex`

Rationale:
BOARD 有 union-of-equations zero-locus = intersection (B-609) 和 singleton zero-locus exactness (B-585), 但通用 inclusion → 反向 inclusion 的 antitone 定理未列。它是零点集分类的核心 order bridge, 比 union 公式更结构化, 证明短且不重复 union 路径: 对 E 中任一方程经 inclusion 转到 F, 再用 F-zero witness。

---
