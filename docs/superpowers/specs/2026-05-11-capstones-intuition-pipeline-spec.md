# Spec: capstones-as-intuition + gate-only harness for theory growth

状态: **v5 final — gate-only philosophy, user 批准 2026-05-11**
日期: 2026-05-11
范围: BEDC 项目 `papers/bedc/parts/visions/` 与 `papers/bedc/parts/concrete_instances/` 的角色 + AI 自动化管线 admission protocol

---

## 0. 一句话目的

**所有 AI 工作只受 gate 约束, 无 blanket 禁令. user 在 capstones 写自由 prose 直觉, AI 通过 TasteGate + ground_compiler 编译器要求自主筛选 candidate, 在任何目录建任何符合 gate 的章, 让理论有序生长**.

---

## 1. 设计哲学: gate-only harness

**核心原则**: AI 可以做任何事, 只要通过所有适用的 gate. spec 不列"AI 不能做什么", 只列"gate 是什么".

**为什么**: 显式禁令清单会随时间膨胀 + 不能预见新场景 + 让 AI 陷入"先检 deny list 再 reason"的低效模式. gate-only 把判断变成结构化属性检查, 可机检, 可扩展, 可让 AI 自主推理"我这次工作通过 gate 吗".

**适用范围**: 本 spec 内所有约束都以 gate 形式表述. user 端只有 *软* STOP signals (在 capstone narrative 写 SCHEMA-ONLY 等), 不是 gate, 不强制 AI.

---

## 2. 三个角色 (按 gate 定义, 不按权限)

### 2.1 capstones/ — user-priority 直觉入口

- user 是默认作者, 自由 prose, 无语法要求
- AI 也可写 capstones, **当且仅当**通过 §4 列的所有适用 gate
- 现有 17 capstones 是 working state, 不动主体

### 2.2 concrete_instances/ — 主要生长区

- AI 是默认作者 (受 §5 增长纪律 gate)
- user 也可写 (历史上 RH chain 是 user 一次性创建)
- 现有 262 章 + 55 子目录是 working state

### 2.3 TasteGate framework — 定义"独立理论"的 gate (已存在)

- `papers/bedc/parts/visions/theory_stability_taste_gate.tex` — 4 义务定义
- `papers/bedc/parts/ground_compiler/` 28 章 — 编译器要求实施
- `lean4/BEDC/Meta/TasteGate.lean` — `ChapterTasteGate X` Lean class
- working examples: `BeliefUp` / `PolicyUp` TasteGate 实例

---

## 3. user 的写作合约

### 3.1 capstones 写法 — 完全自由

user 写任何形式: 概念身份 / 路线图 prose / 桥定理 / 哲学叙事 / 显式 SCHEMA-ONLY 标注. 无新语法要求.

### 3.2 user 的 4 个 STOP signals

| Signal | 形式 | AI 行为 | gate 类型 |
|---|---|---|---|
| 散文 STOP | "SCHEMA-ONLY" / "deferred to future" / "not yet developed" 字样 | candidate 进 `deferred_candidates`, 不提案 | **hard** (G_capstone_stop_respect, §4.3) |
| Emergency brake | `papers/bedc/.creation_paused` 文件 | 拒绝所有新章 P-round | **hard** (G_emergency_brake, §5.3) |
| Veto 既成事实 | user `git revert` | AI 下轮重新评估 | soft (无显式 gate, 靠 git state) |
| 编辑 capstone narrative | user 改 prose | AI 下轮重新读 | soft (无显式 gate, 靠下轮 read) |

(前两个是 hard gate, 机检强制; 后两个是软 — 不需 gate, AI 自然在下轮 P-round 重新读时反映 user 的变更.)

---

## 4. AI 的 gate 集合 (替代任何 "AI 不能做什么")

AI 任何 P-round / R-round commit 必须**同时通过**以下所有适用 gate. 通过 = 工作合法. 不通过 = commit 拒绝 / round abort.

### 4.1 现有 gate (全部保留)

| Gate | 来源 | 适用范围 |
|---|---|---|
| **G_axiom_purity** | `tools/check-axioms.py` + `bedc_ci.py axiom-purity --strict` | Lean 端任何 declaration |
| **G_no_axiom** | `tools/check-axioms.py` | `lean4/BEDC/` 不得有 `axiom` 关键字 |
| **G_no_sorry** | (现行 invariant) | `lean4/BEDC/` 不得有新 `sorry` 占位 |
| **G_anti_hollow** | `phase_b.txt` §"Anti-hollow semantic discipline" | Lean target 不得 Unit / True / 占位 |
| **G_no_nursery_shell** | `phase_b.txt` §"No nursery-shell growth" | 拒绝 parameter echo / abstract shell |
| **G_naming_decomp** | `lean4/NAMING.md` + `phase_b.txt` §"Naming and decomposition" | Lean target 命名规则 |
| **G_drift_audit** | `bedc_ci.py audit` | `\leanchecked{X}` 中 X 必须真存在 |
| **G_axis_confusion** | `bedc_ci.py` | closurestatus 双轴不可互相函数化 |
| **G_orphan_subdir** | `bedc_ci.py detect_orphan_concrete_subdirs` | concrete_instances 子目录名 = 真 region |
| **G_conservativity** | `bedc_ci.py conservativity-audit` | ai-proposed 不泄漏到 baseline import |
| **G_max_800_lines** | `scripts/check_tex_size.sh` | 单 .tex ≤ 800 行 |
| **G_no_iteration_narrative** | `scripts/check-iteration-narrative.sh` (现行) | 不出现 "新增/v1.5.X/legacy" 等字样 |
| **G_no_banned_math_env** | `scripts/check_math_env.sh` | 不用 `\[...\]` / `\begin{equation}` 等顶层禁用环境 |
| **G_tree_wide_dedup** | `phase_b.txt` §"tree-wide semantic dedup" | 同 conclusion 不可重复 declaration |
| **G_theme_saturation** | `phase_revise.txt` (升级到 §5.2) | 同主题文件数 ≥ 80 拒新主题顶层 |

### 4.2 新增 G_taste_gate_feasibility (核心新 gate)

任何 `theory_extension` target 提案 (尤其 `flavor = "human_chapter_extension"`), 必须在 `notes.taste_gate_feasibility` 5 字段非空:

- `bhist_carrier_sketch`: 一段话, 显示 X-token 如何嵌入 BHist 或 BHist-参数化结构. 若需 unboxable infinite parameter / non-BHist primitive → 写 "fails", gate 拒绝.
- `conservativity_argument`: 一段话, 显示 admitting X 不破现有定理可证性, 新可证定理必 mention X. 引用 `\autoref{ch:ground-compiler-...}`.
- `no_hidden_input_argument`: 一段话, 显示 X-token 是 `\bzero, \bone` 显示出来的有限事件流的识别像. 引用 `ch:ground-compiler-event-flow`. fails → 拒绝.
- `round_trip_argument`: 一段话, 显示 display readback ∘ reconstruction = identity on tokens. 引用 `ch:ground-compiler-zeckendorf-safe-channel-encoding` 的 `flow_level_round_trip`. fails → 拒绝.
- `layer_separation_argument`: 一段话, 显示 source/channel/display 三角色不坍缩. 引用 `ch:ground-compiler-source-channel-layer-separation`. fails → 拒绝.

实施: `phase_review.txt` 加 ~50 行 HARD GATE 段; `phase_d_lint` 加 ~20 行机检 (5 字段非空, 任何"fails"字串触发拒绝).

不通过 = round abort. 通过 = candidate 进 candidate_pool, 由下游优先级排序决定是否当轮实施.

### 4.3 新增 G_capstone_stop_respect (hard gate, D2 锁定)

当 AI 考虑的 candidate 概念在某 capstone 文件中, **该概念所在的 nearest containing block** (即包围该 mention 的最内层 `\section{...}` / `\subsection{...}` / `\paragraph{...}` 或独立段落, 若都无则整章) 包含 STOP 字样 ("SCHEMA-ONLY" / "deferred to future" / "not yet developed" / "future development that does not yet exist") → candidate 必须进 `deferred_candidates[]`, 不进 candidate_pool.

实施: `phase_review.txt` 加 ~25 行 HARD GATE 段; `bedc_ci.py` 加 ~30 行 audit. 实施细节:
- AI 在 P-round commit message 的 transparency 字段必须暴露每个 candidate 的 `source_location: "capstones/<theme>.tex:L<start>-L<end>"` (源自 capstone narrative 的精确行号范围)
- audit 用该 source_location 取出对应 capstone 文本片段, grep STOP 字样
- 若 grep 命中且 candidate 不在 `deferred_candidates[]` → audit fail

不通过 = round abort.

### 4.4 新增 G_derived_from_traceability

任何 P-round 创建的 `human_chapter_extension` 章节, 若其 `taste_gate_feasibility` 任一字段引用了 `parts/visions/<theme>.tex` 中的语句, chapter 顶部必须加:

```latex
\derivedfrom{ch:visions-<theme>}{rationale: "<引述 capstone 中具体话>"}
```

实施: `phase_revise.txt` 加 ~15 行模板; `bedc_ci.py` 加 ~30 行 audit (`<theme>` 存在 + rationale 非空).

不通过 (AI 创建 capstone-derived chapter 但没 `\derivedfrom`) = audit fail.

允许 chapter 无 `\derivedfrom` (若是独立 horizon, 与任何 capstone 无关).

### 4.5 G_capstone_write 统一规则 (替代 v4 "AI 不写 capstones" 的禁令)

**AI 可以触碰 capstones**, 但 commit 必须通过以下:
- 所有 §4.1 现有 gate (axiom-purity / no-sorry / 800-line / iteration-narrative 等)
- 通过 G_taste_gate_feasibility (若添加新 theorem / definition / identification)
- 通过 G_capstone_stop_respect (若区域含 STOP 字样, 不能在该区域写)
- 通过 G_drift_audit (任何 `\leanchecked{X}` 中 X 必须真存在)

**没有额外的"AI 不许写 capstones"禁令**.

实际后果: AI 大概率不会主动写新 capstone, 因为:
- 新 capstone 通常是跨 ≥ 3 horizon 的 bridge → 必先有这些 horizon 在 concrete_instances/
- 已有的 `meta_capstone` flavor 配 `capstone_overlap_map` 已存在, AI 已自主提案 meta-capstone (60 天经验 0-2 次)
- 大部分 capstone 内容是 user 思考, AI 提案的桥定理不符 capstone narrative 风格, gate 不会单独 reject 但 user 会 git revert

所以 capstones 的 user-priority 性质**自然**来自 gate + AI 的工作激励 (critical_path scoring 主要在 concrete_instances), 不需要显式禁令.

### 4.6 P-round 必须暴露的 4 个 transparency 字段 (gate 要求)

每个 P-round commit 的 message body 必须包含一个 ` ```transparency` fenced YAML block:

```yaml
proposed_candidates:
  - name: <X>Up
    source_capstone: <theme>                  # capstone 文件 stem, 无则 null
    source_location: <file>:L<start>-L<end>  # 精确行号 (G_capstone_stop_respect audit 用)
    taste_gate_feasibility:                  # G_taste_gate_feasibility 5 字段
      bhist_carrier_sketch: <一段话>
      conservativity_argument: <一段话>
      no_hidden_input_argument: <一段话>
      round_trip_argument: <一段话>
      layer_separation_argument: <一段话>

rejected_candidates:
  - concept: <概念名>
    source_capstone: <theme>
    source_location: <file>:L<start>-L<end>
    failed_obligation: bhist_carrier_sketch | conservativity | no_hidden_input | round_trip | layer_separation
    rationale: <一句话>

deferred_candidates:
  - concept: <概念名>
    source_capstone: <theme>
    source_location: <file>:L<start>-L<end>
    stop_marker_text: <引述 STOP 字样的具体句>

implemented_targets:
  - name: <X>Up
    file: papers/bedc/parts/concrete_instances/<NN>_<slug>_namecert_construction.tex
    derivedfrom: ch:visions-<theme>  # 若有
```

实施: `phase_revise.txt` 加 commit message 模板 (~30 行); `bedc_ci.py` 加 YAML 解析 (~20 行).

未暴露 (或解析失败) = audit warn (不 fail, 因为这是可见性问题, 不是 invariant 违反). 但 G_capstone_stop_respect 与 G_taste_gate_feasibility 都依赖 transparency 字段读 source_location 与 5 字段, 缺失会导致那两个 gate fail (因无法机检).

---

## 5. concrete_instances 增长纪律 gate

### 5.1 G_daily_rate (L1)

24 小时内全 worker 合计新建顶层 `<NN>_<slug>_namecert_construction.tex` ≤ 10. 检测: `git log --since="24 hours ago" --diff-filter=A`. 超出 → `codex_revise.py` 在 P-round commit 前 reject.

阈值 10 可在 `.pipeline_parallel.json` 加 key `daily_new_chapter_cap` 覆盖.

子目录 sibling 文件创建不算 (已有章节深化).

### 5.2 G_theme_saturation_enhanced (L2)

现行: 60 天 ≥ 6 commit 同主题即饱和. 升级: 同主题已有顶层 + 子目录文件总数 ≥ 80 时禁新主题顶层章.

例: `field/` 137 文件 + `20_field_namecert_construction.tex` = 138 > 80 → 禁新 `_field*` 前缀顶层章.

已有章节延伸不受影响.

### 5.3 G_emergency_brake (L3)

`papers/bedc/.creation_paused` 文件存在时, `codex_revise.py` 拒绝所有 `new_files` 含 `parts/concrete_instances/<NN>_*_namecert_construction.tex` 的 P-round.

user 单边切换: `touch .creation_paused` / `rm .creation_paused`.

### 5.4 G_nn_atomic_claim

`codex_revise.py` 用 `fcntl.flock` 在 `.worktrees/.nn_claim.lock` 上原子 claim 下一个可用 NN. 写 `.worktrees/.nn_claimed/{NN}.txt` 占位防并发. commit 后释放.

已存在 race (271×3 / 272×2 / 273×4 / 301 跳号) 不回滚, lint warn 不 fail.

---

## 6. CI gate 实施 (bedc_ci.py + codex_revise.py)

### 6.1 新增 audit (~150 行总)

1. **G_taste_gate_feasibility** (~30 行 in `bedc_ci.py`): 扫 P-round commit message body, 检查 5 字段非空, 任一 "fails" 字串 → audit fail
2. **G_capstone_stop_respect** (~30 行): 扫提案 candidate 是否在 capstones 中 STOP 标注区域
3. **G_derived_from_traceability** (~30 行): `\derivedfrom` 解析 + `<theme>` 存在性 + rationale 非空
4. **G_daily_rate / G_theme_saturation_enhanced** (~40 行 in `codex_revise.py`): commit 前 check
5. **G_nn_atomic_claim** (~20 行 in `codex_revise.py`): `fcntl.flock` 实施

### 6.2 现有 audit 保留

15 个现有 gate 全保留, 无改动 (axiom-purity / no-sorry / drift / orphan-subdir / conservativity / 800-line / iteration-narrative / banned-math-env / tree-wide-dedup / naming-decomp / anti-hollow / no-nursery-shell / axis-confusion / orphan / 现行 theme-saturation 升级).

---

## 7. 实施 phases

### Phase 1: prompt 改动 (~0.5 天)

1. `phase_review.txt`: 
   - 加 HARD GATE G_taste_gate_feasibility (~50 行)
   - 加 HARD GATE G_capstone_stop_respect (~25 行)
   - 加 transparency 字段说明 (~15 行)
2. `phase_revise.txt`: 加 `\derivedfrom` 模板 + commit message 模板 (~30 行)

### Phase 2: gate 实施 (~1 天)

1. `bedc_ci.py`: G_taste_gate_feasibility + G_capstone_stop_respect + G_derived_from_traceability 三 audit (~90 行)
2. `papers/bedc/preamble.tex`: `\derivedfrom` 宏定义 (~5 行)

### Phase 3: 增长纪律 gate (~1 天)

1. `codex_revise.py`: G_daily_rate + G_theme_saturation_enhanced + G_emergency_brake + G_nn_atomic_claim (~80 行)
2. `bedc_ci.py`: NN race lint warn (~15 行)

### Phase 4: test (~半天)

测试 fixture: **`inter_hist_locality.tex`** (自带 6 个 SCHEMA-ONLY 标注)

不动 capstone 主体. 跑 1 个 P-round, 预测:

- AI 读 inter_hist_locality, 抽 candidates (MultiHistConfig / CrossHistCausal / MaxCausalRate / Lorentz / Curved spacetime / etc.)
- 各跑 G_taste_gate_feasibility
- 大部分 candidate 区域含 SCHEMA-ONLY → G_capstone_stop_respect 把它们推进 `deferred_candidates`
- 少数 (e.g. "Ledger-local relations", 不在 SCHEMA-ONLY 区域) → 通过 G_capstone_stop_respect → 跑 G_taste_gate_feasibility → PASS / FAIL
- PASS 的 → 进 candidate_pool → 当轮可能实施
- FAIL 的 → 进 `rejected_candidates`

**success 标准**:
- commit message / critical_path JSON 出现非空 `rejected_candidates` 或 `deferred_candidates`
- 若有 PASS candidate, chapter 含 `\derivedfrom{ch:visions-inter-hist-locality}{...}`
- 所有 gate 没 false positive (合法工作未被错拒)
- 所有 gate 没 false negative (不合法工作未被错放)

**failure 模式 + 修复**:
- AI 不读 STOP signal → 调 phase_review.txt G_capstone_stop_respect 措辞
- TasteGate 评估全 PASS 但实际不可行 → 调 phase_review.txt G_taste_gate_feasibility 措辞 (要求更严格的 ground_compiler 引用)
- chapter 不加 `\derivedfrom` → 调 phase_revise.txt 模板

---

## 8. 验证标准

### 8.1 gate 设计正确

- Phase 4 test 出现 `rejected_candidates` / `deferred_candidates` 非空字段 → gate 在工作
- chapter 出现 `\derivedfrom` 反向 cite → traceability 链路通
- inter_hist_locality 大部分 candidate 因 STOP 进 deferred (不是因 TasteGate fail) → G_capstone_stop_respect 工作正常
- 少数没被 SCHEMA-ONLY 覆盖的概念走完 G_taste_gate_feasibility 流程 → admission gate 工作

### 8.2 gate 在 30 天部署的运行指标

- G_daily_rate 触发拒绝 ≥ 1 次 (说明 rate limit 实际生效)
- G_theme_saturation_enhanced 触发拒绝 ≥ 1 次 (说明真有膨胀压力)
- G_emergency_brake user 用过 ≥ 1 次 (说明 brake 可用)
- G_nn_atomic_claim 0 race 新增
- G_taste_gate_feasibility 拒绝率 = `rejected_candidates / proposed_candidates` ∈ [10%, 60%] (太低 = gate 流于形式; 太高 = AI 提案质量低)

### 8.3 直觉传递率 (60 天)

- 含 `\derivedfrom` 的 concrete_instances chapter 数 ≥ 20
- `rejected_candidates` 累计 ≥ 5
- `deferred_candidates` 累计 ≥ 10 (SCHEMA-ONLY signal 真在生效)

---

## 9. 风险与边界

### 9.1 风险

1. **G_taste_gate_feasibility 流于形式 — 5 字段都填"plausibly OK"**
   - 缓解: R-round 实际构造 `ChapterTasteGate X` Lean 实例时, 字段不能 Unit / True.intro. P-round feasibility 错估 → R-round 卡住 → 下个 P-round revert chapter. **gate 之间互相验证**.
   - 监控: 60 天后看 ai-origin chapter 实际 R-round 实现率. <80% 实现 → P-round feasibility gate 失效, 加严措辞.

2. **AI 漏读 STOP signal**
   - 缓解: G_capstone_stop_respect 是机检 gate (bedc_ci.py 实施, 不只靠 AI 自觉). 实际 STOP 区域提案 → audit fail → round abort.

3. **`\derivedfrom` rationale 形同空文**
   - 缓解: rationale 必须引述 capstone narrative 中具体话 (audit 要求字段非空, 内容质量靠 user spot-check via `rejected_candidates`/`deferred_candidates` 暴露)

4. **L1 rate limit 阻塞正当快速生长**
   - 缓解: 阈值 10 可调

5. **多 worker 抢同 capstone narrative 同 candidate**
   - 缓解: NN claim lock 扩展到 chapter-name claim (`.worktrees/.chapter_name_claimed/<X>Up.txt`)

### 9.2 兼容性

所有现有 invariant 保留:
- CLAUDE.md "禁止迭代叙事" → G_no_iteration_narrative
- CLAUDE.md "Hub-only 索引文件" → 不变
- CLAUDE.md "禁止 axiom" → G_no_axiom
- CLAUDE.md "0 sorry" → G_no_sorry
- CLAUDE.md "800 line cap" → G_max_800_lines
- f66625f97 "AI-origin gate-less" → **完全兼容** (TasteGate 是 admission gate, 不是 user accept gate. AI 自主跑 TasteGate, 不需 user 干预.)

---

## 10. 文件改动清单

新文件: 无

修改:
- `papers/bedc/scripts/prompts/phase_review.txt` — 加 3 个 HARD GATE 段 + transparency 字段说明 (~90 行)
- `papers/bedc/scripts/prompts/phase_revise.txt` — 加 `\derivedfrom` 模板 + commit message 模板 (~30 行)
- `papers/bedc/preamble.tex` — 加 `\derivedfrom` 宏 (~5 行)
- `papers/bedc/scripts/codex_revise.py` — 加 L1/L2/L3 + NN claim lock (~80 行)
- `lean4/scripts/bedc_ci.py` — 加 4 新 audit (~120 行)

**总改动**: 5 文件, **~325 行**. 估计 2-3 天 (Phase 1+2+3) + 半天 (Phase 4 test).

不动文件 (全部为现有 working state, 不需要 spec 触碰):
- 17 capstones 主体
- 262 concrete_instances 章节
- ground_compiler 28 章
- `lean4/BEDC/Meta/TasteGate.lean` + BeliefUp / PolicyUp 实例
- main.tex / lakefile.lean / lean-toolchain
- `lean4/BEDC/Derived/Observer.lean` (19 个 True.intro 占位 — 若 user 后来想填, 可 trigger 新 P-round)
- field/ 137 文件 no-hub (与本 spec 无关)
- main.tex 263 行 \input (与本 spec 无关)

(注: 这些"不动"是因为 **不在本 spec scope**, 不是因为禁止改. 若有需要可独立处理.)

---

## 11. 关键 reframing: v4 → v5

| 维度 | v4 | **v5 (finalized)** |
|---|---|---|
| 哲学 | enumerate "AI 不能做什么" | gate-only: enumerate "通过什么 gate 才合法" |
| §2 长度 | 12 条 "不做的事" prohibition list | "三个角色按 gate 定义" (无 prohibition) |
| AI 写 capstones | T1 完全禁止 (blanket ban) | G_capstone_write = 同一套 gate 适用 (无单独 ban) |
| 列了什么 gate | 隐式, 散在文中 | §4 一张表显式列 15 个现有 + 4 新 gate |
| user-priority 性质 | 靠 explicit prohibition 强制 | 靠 gate + 工作激励 (critical_path scoring) 自然涌现 |
| 改动量 | ~270 行 | ~325 行 (多 ~55 行因为加 G_capstone_stop_respect 机检) |
| 是否给 AI 留预期外的自由 | 否 (deny list 锁死) | **是** (AI 可创新, 只要 gate pass) |

v5 是把 BEDC 项目"通过 gate 自主生长"的 harness 哲学贯彻到底. 这与 f66625f97 commit "operator-bottlenecked from day one is anti-pattern" 同方向.

---

## 12. user 锁定的 3 个决定 (2026-05-11)

**D1**: G_taste_gate_feasibility 5 字段 **全部强制非空**. 任一 "fails" → round abort. Conservativity 不软评. (Phase 4 后视实证情况决定是否调措辞.)

**D2**: G_capstone_stop_respect 是 **hard gate**. audit fail = round abort. AI 不可 override SCHEMA-ONLY 区域的提案.

**D3**: Phase 4 test fixture = **`inter_hist_locality.tex`**. 不动 capstone 主体, 利用其 6 个自带 SCHEMA-ONLY 标注作天然 fixture.

---

**spec 结束**. 下一步: `writing-plans` skill 起 implementation plan.
