# TASTE_GATE_FRAMEWORK_PLAN

## 总体愿景: 理论自主健康生长

让 AI 发现 *真实的* 新理论, 不只是 combinatorial 凑数。三个关键词:

**自主**: 系统主动识别 frontier 饱和 (closed/open > 阈值) → 主动 propose 新章节 →
TasteGate audit 过滤 → 操作员决策 → 进入 horizon → paper / lean round 自动推进。
人不应该是新章节的瓶颈 (操作员只在 review 步骤介入, 越往后比重越低)。

**健康**: 每一步都有 machine-checkable 的 taste gate, 而不是隐性数学品味。
新章节不能通过简单 rename 老章节、cartesian product 凑数、或偷渡 mathlib 公理
进入系统。TasteGate 的四条 obligation (conservativity / no_hidden_input /
round_trip / layer_separation) 是机器版同行评审, 比人审更严格、更快、更
consistent。

**生长**: 系统在 frontier 上持续扩张, 不退化。已 mature chapter 不被回退;
新 chapter 被 absorbed 时其他 chapter 的 invariant 不被破坏 (这正是
conservativity 保证); frontier 沿着"从 BEDC kernel 到 AI / agent / 实证科学
边界" 的方向移动。

四个 phase 对应这三条:

```
Phase 0   → framework 可执行, 让"健康"有 machine-checkable 形式
Phase 1   → active gate, 让"健康"在所有 ai-proposed chapter 强制
Phase 2   → propose 路径开放, 让"自主"开始有触发机制
Phase 2.5 → auto-trigger 接入, 让"自主"完全去人化 (除 review 步骤)
Phase 3   → 长期校准 + meta-discovery, 让"生长"具有动量与方向感
```

成功判据:

- 短期 (Phase 1+2 落地): 至少 1 个 ai-proposed chapter 通过 TasteGate 进
  matureClosure, 与 280+ 现有 human-curated chapter 共存于 horizon.
- 中期 (Phase 2.5 + 1-2 月): codex 自主 propose 命中率 > 30%, 累计 ≥ 10 个
  ai-proposed chapter 通过 TasteGate 进 matureClosure, 操作员 review 单次平
  均耗时 < 5 分钟.
- 长期 (Phase 3 + 持续): ai-proposed chapter 与 human-curated chapter 互
  cite (ai chapter 用作 human chapter 的 dependency 锚点), 表明 AI 发现的
  理论在 BEDC 内部具有真实结构性贡献.

底线: TasteGate 没有捕捉到 false negative (假理论过 gate) 在持续 6 个月内 = 0;
false reject (真理论被 gate 拒绝) 通过 reference instance audit + 人工
override 机制收敛到 < 5%。

## 背景

BEDC 当前 280+ chapter 全部是 *人类已发现的数学* 的形式化——继承数学共识背书，每个 chapter 对应历史上经过反复 stress-test 的真理论 (Group / Hilbert / Curvature / GelfandDuality 等)。下一阶段是让 codex 自主发现 / propose 新理论 (AI agent / alignment / 信息论延伸 / causal inference / 计算机系统验证)，但这种"AI propose 的新章节"没有数学共识背书，可能是 combinatorial 凑数、已有章节的同义重命名、BEDC 0-axiom 边界外的 hallucination、或 chapter 自己 self-consistent 但加进系统破坏其他章节稳定性。

ground_compiler 章节 (papers/bedc/parts/ground_compiler/, lean4/BEDC/GroundCompiler/) 的核心定理 (`*_conservativity` / `no_hidden_input` / `flow_level_round_trip` / `source_channel_separation`) 不是关于"如何编译"，而是关于"什么是 invariant under recognition"——回答元问题 *"一个对象是否真的存在 independent of representation choice?"* 这恰好是数学家对"真理论"的隐性判据：可换 representation 不改变本质 (双射)；可嵌入更大 system 不增证明能力 (保守扩张)；不偷渡外部假设 (no hidden input)。

把 ground_compiler 的元定理升格为 **chapter-level taste gate**，给 AI propose 的新章节加一组机器可检验的 quality control，把"什么是真理论"从 prompt-level 隐性指令变成 lean-level 机器检验。

## 应用范围

**Human-curated chapter** (现有 280+ + 操作员手动种子化的): **不需要** TasteGate
- 数学共识已经替我们做了 taste audit
- 操作员手动 seed (像 2026-05-10 加的 8 个新 chapter) 继承 human curation credit

**AI-proposed chapter** (codex 自主 propose 路径, Tier 2/Tier 3): **必须** 过 TasteGate
- 没有数学共识背书
- TasteGate 充当机器版同行评审

区分依据: closurestatus 块的 `\origin{human|ai}` 字段 (Phase 1 引入)

## 总体策略

**双轨并行**:
- 编译器最后 40% (ch18-28 prototype 实现层) 在独立分支 `ground-compiler-formalize` 跑
- TasteGate 在 codex-auto-dev 主干推进
- 两者不冲突: TasteGate 抽接口需要的元定理 100% 已在 codex-auto-dev 的 `lean4/BEDC/GroundCompiler/MainTheorems.lean` + `EventFlow.lean` + `RecognizerFlows.lean` 等模块里
- 剩 40% 是 prototype 应用层, 不引入新元定理, 接口稳定

## TasteGate 接口设计

四个 obligation, 每个对应 ground_compiler 的一组元定理:

```lean
structure ChapterTasteGate (X : Type) [BHistCarrier X] where
  -- 1. 加 X 不让 baseline 既证定理变 unprovable / unprovable 变 provable
  conservativity_witness :
    ∀ (φ : BaselineFormula),
      Provable (Baseline ∪ {X}) φ ↔ Provable Baseline φ ∨ MentionsX φ

  -- 2. X 的所有 carrier 行可由 BHist 上 finite history 显式生成
  no_hidden_input_witness :
    ∀ (h : X.carrier), ∃ (e : EventFlow), X.recognize e = some h

  -- 3. readback ∘ reconstruct = id (representation-independent)
  round_trip_witness :
    ∀ (h : X.carrier), X.reconstruct (X.readback h) = h

  -- 4. X 的 source / channel 角色严格分离
  layer_separation_witness :
    SourceChannelSeparated X
```

设计原则: **既严格又可达**
- 严格: 通过 taste_gate 等于真理论 (高置信度)
- 可达: 人类已知真理论都能通过 (5-8 个 reference instance 必须过)

不能让 typeclass 太严以至于连 GroupUp / HolomorphicUp 都过不了——这意味着 TasteGate 要在抽象层捕捉 *理论 invariance*, 不要陷入实现细节。

### 设计教训: 不要让 chapter 自由出题

第一版 (Phase 0 commit `48d3f9c86`) typeclass 写成:

```lean
structure ChapterTasteGate (X : Type) where
  conservativity_holds : Prop
  conservativity_proof : conservativity_holds
  ...
```

每个字段都让 chapter 自由选 `Prop`。结果 codex 第一次为 BeliefUp 写
instance 时, 4 个 obligation 全用 vacuous 命题 (`∀ n : Nat, n = n`)
discharge——题目和答案都是 chapter 自己出的, 不是 quality control 而是
self-grading。任何 chapter 都能用同样的 trivial 占位通过。

第二版 (Phase 0.5 commit `82b71d1a6`) schema-enforced typeclass:

```lean
class BHistCarrier (X : Type) where
  toEventFlow : X → EventFlow
  fromEventFlow : EventFlow → Option X

class ChapterTasteGate (X : Type) [BHistCarrier X] where
  conservativity   : ∀ (x : X) (w : RawEvent) (m : DisplayAlphabet),
                       List.Mem w (toEventFlow x) → List.Mem m w →
                       m = b0 ∨ m = b1
  no_hidden_input  : ∀ (x : X), ∃ (e : EventFlow),
                       fromEventFlow e = some x
  round_trip       : ∀ (x : X),
                       fromEventFlow (toEventFlow x) = some x
  layer_separation : ∀ (x y : X), x ≠ y →
                       toEventFlow x ≠ toEventFlow y
```

每个 obligation 类型里都强制出现 `X` 和 `BHistCarrier.toEventFlow` /
`fromEventFlow`, 所以:

- chapter 必须先给 inductive `X` 才能 instance `BHistCarrier`.
- chapter 必须真的定义 `toEventFlow : X → EventFlow` 这条 embedding,
  这是把"chapter 本身"具体化的步骤.
- `round_trip` 和 `layer_separation` 都需要 case-split on `X` 的
  constructor, 不能用 `True.intro` 通过.
- `Unit` 单元素类型仍可写 instance, 但 `layer_separation` 在
  `∀ x y, x ≠ y → ...` 上 vacuously true, 是 quality 警示而非 escape
  hatch—— typeclass 默认要求 chapter 至少有 2 个 distinct constructor
  (BeliefUp 用 `empty | observed` 这种最简形式).

教训: **typeclass 字段不能是 raw `Prop`. 必须用 dependent types 让
obligation 类型依赖 chapter carrier**, 这样 codex 不能用 schema-外
trivial 命题 discharge。这条规则也适用于未来任何"AI quality control"
gate 设计——schema 必须 pin 到被审视的对象.

## Phase 0 — 现在做 (无 active gate)

**目标**: framework 落地, 不动 audit / phase prompt, framework 静默存在。

**改动**:

```
lean4/BEDC/GroundCompiler/TasteGate.lean                              新建 (200-300 行)
  ├── structure ChapterTasteGate (X : Type) [BHistCarrier X]
  ├── 复用 GroundCompiler.MainTheorems / EventFlow 等已有定理作为
  │   typeclass 字段的实现模板
  ├── lemma template helpers (让新 chapter 不用从零证)
  └── reference instance 5-8 个:
      ├── TuringMachineUp (必须, 跟 ground_compiler 紧密相关)
      ├── NatUp / GroupUp / HolomorphicUp / QuantumStateUp (公认真理论)
      └── 1-2 个边界例子 (验证某种应该 reject 的 chapter 确实过不了)

papers/bedc/parts/visions/theory_stability_taste_gate.tex            新建
  └── 描述 framework: 4 条 obligation 的数学含义 + 与 NameCert
      5 obligation 的关系
      (TasteGate 是 cross-chapter / cross-layer, NameCert 是
      chapter-internal, 两者 orthogonal)

papers/bedc/preamble.tex                                               改
  └── \newcommand{\TasteGate}{...}
      (此阶段不加 \origin 宏, 等 Phase 1)

CLAUDE.md / AGENTS.md / SKILL.md                                       改
  └── 新增 "TasteGate framework" section (描述 framework + 应用范围)
```

**验证**:
- `cd lean4 && lake build` exit 0, 5-8 个 reference instance 全过
- `python3 lean4/scripts/bedc_ci.py audit` exit 0
- `python3 tools/check-axioms.py` exit 0
- `cd papers/bedc && make` 双趟通过, PDF 含新 capstone 章节
- `python3 lean4/scripts/bedc_ci.py axiom-purity --strict` 通过

**输出**: 没有任何 active gate, pipeline 不受影响, 操作员 + codex worker 行为不变。framework 在 lean tree 里 *有可执行 instance*, 但还不强制。

**时间**: ~1 天

**风险**: 极低。仅新建模块, 无 active enforcement。最坏情况是 typeclass 接口设计不够好, 5-8 个 reference 过不了——可以反复 iterate 接口直到 reference 都过。

**Status: completed 2026-05-10 (commit 48d3f9c86)**
- TasteGate.lean shipped 1 reference instance (groundCompilerSelfTasteGate, backed by event_flow_conservativity / no_hidden_input / flow_level_round_trip / True placeholder for layer_separation)
- theory_stability_taste_gate.tex shipped (full capstone chapter)
- 5-8 reference instance 实际只发了 1 个 (ground compiler self) — 其他 reference instance 推到 Phase 1+ 再补充 (因为 GroundCompiler 60% ship 已足够支撑 framework, 不阻塞下一阶段)
- 没等 PR #50 100% ship — 用户 2026-05-10 决定 codex-auto-dev 是开发分支, 不必等独立 PR

**Decision Gate (Phase 0 → Phase 1)**:
- 5-8 个 reference instance 全过 lake build → 部分满足 (1 个 ship)
- typeclass 接口在 60% ground_compiler 上稳定 → 已确认

## Phase 1 — 编译器 100% ship 后启动 (active gate, 仅 ai_proposed)

**目标**: TasteGate 从静默 framework 升格为 active gate, 但仅对标记为 `\origin{ai}` 的 chapter 生效, 现有 280+ human-curated chapter 完全不受影响。

**改动**:

```
papers/bedc/preamble.tex                                改 closurestatus 环境
  └── 增加可选字段 \origin{human|ai}
      默认 human (省略时按 human, 不要求 TasteGate)

lean4/scripts/bedc_ci.py                                改 audit
  ├── 规则: \origin=ai 的 chapter 必须 cite
  │   \leanchecked{BEDC.Derived.<X>Up.taste_gate}
  │   才能进 obligationClosure 以上
  └── \origin=human 的 chapter 不变
      (现有 280+ chapter 全部继承 human credit, 不需要补 TasteGate
      instance, 也不会被 audit fail)

papers/bedc/scripts/prompts/phase_review.txt           改 v4.x → v5.x
  └── 增加 "AI-proposed chapter MUST have TasteGate instance"
      hard gate

lean4/scripts/prompts/phase_c.txt                      改 v5.14 → v5.15
  └── 增加 "creating <X>Up file with \origin=ai requires
      BEDC.Derived.<X>Up/TasteGate.lean instance" hard gate
```

**输出**: active gate 启用。新写的 chapter 如果声明 `\origin{ai}` 必须过 TasteGate; `\origin{human}` 走旧路径不受影响。

**时间**: ~半天

**风险**: 低。区分 origin 让现有 280+ chapter 完全不被影响。最大风险是 audit 误伤——某个未标 origin 的 chapter 被错判为 ai。Mitigation: audit 默认空 origin = human, 只有显式标 ai 才严格化。

**Status: part A completed 2026-05-10 (commit 5b78cbc6c); part B deferred**
- preamble.tex \origin field 已加 (default human)
- bedc_ci.py audit gate 已加 (\origin=ai 过 seedClosure 必须 cite TasteGate instance)
- audit gate 已 active 但当前无 \origin=ai chapter 存在, gate 不触发, backward-compat
- Part B (phase_review/phase_revise hard gate 改动) 推迟: 现有 paper round 100% 在做现有 chapter 的 closure_mark, 跟 \origin/TasteGate 无关; phase_review 加 prompt 信息只增加 token cost 和 hallucination 风险, 实际 trigger 路径是 phase_propose (Phase 2). 等 Phase 2.5 auto-trigger 启用时再考虑

**Decision Gate (Phase 1 → Phase 2)**:
- TasteGate gate 在 1 周内不引发已有 chapter 误伤 → 监控中
- 至少有 1-2 个手动种子化但标记为 `\origin{ai}` 的 reference chapter 过 gate → 待 first ai-proposed chapter
- pipeline 持续 0 audit fail → 监控中

## Phase 2 — Tier 2 propose 路径开放 (依赖 Phase 1)

**目标**: 让 codex 自主 propose 新 chapter, TasteGate 自动充当 quality filter, 操作员只做最终审核。

**改动**:

```
papers/bedc/scripts/prompts/phase_propose.txt          新建
  ├── 触发条件:
  │   ├── closed/open > 2 (frontier 饱和)
  │   ├── 上次 propose 已超 N round
  │   └── critical_path top[0..2] labels = 0 (现有 top 没有可推工作)
  ├── 输出格式:
  │   papers/bedc/proposals/<sha>_<slug>.md
  │   包含: chapter name, carrier sketch, 4 个 TasteGate obligation
  │   sketch, ≥3 个 dependency chapter
  └── 严格约束:
      ├── chapter 必须 cite ≥3 现有章节作 dependency (防孤岛)
      ├── constructivestory 必须出现 BHist / hsame / Cont / Pkg
      ├── 不准 import 任何在现有 lean tree 里没出现过的数学概念
      │   (防 codex 偷渡 mathlib 风格)
      └── propose 的 carrier 必须有 4 obligation 的 sketch
          (不要求完整证明, 但要求有可信 outline)

papers/bedc/proposals/                                 新建目录
  └── README.md: review 流程 + accept/reject 规则
      ├── proposal 文件命名: <commit-sha>_<slug>.md
      ├── accept: 操作员把它升格成正式 stub (走标准 seed 流程,
      │           标 \origin{ai})
      └── reject: 留在 proposals/ 作为反例, feedback 给
                   phase_propose prompt

papers/bedc/scripts/codex_revise.py                    改
  └── 加 phase_propose 触发条件 + 调用机制
      (在每 N 个 paper round 之间, 满足 trigger 时跑 1 次 propose)

lean4/scripts/review_proposals.py                      新建
  └── 列出待审 proposal + 自动检查 dependency / TasteGate sketch
      + 操作员 accept/reject CLI
      ├── review_proposals.py list
      ├── review_proposals.py show <sha>
      ├── review_proposals.py accept <sha>  (升格为 stub)
      └── review_proposals.py reject <sha>  (留 archive + feedback)
```

**输出**:
- codex 自主 propose 路径开放
- 但每个 propose 必须经操作员 review (品味保险)
- 被 accept 的 proposal 自动种子化进 codex-auto-dev, 标 `\origin{ai}`
- 被 reject 的 proposal 留在 proposals/ 作为反例

**时间**: ~2 天

**风险**: 中。最大风险是 codex propose 命中率太低 (< 30%) → 人工 review 成本过高 → 路径无效。

**Mitigation**:
- 先关 Tier 2 一周, 观察 proposal 质量
- 根据 accept rate 调 phase_propose prompt

**Status: scaffolding completed 2026-05-10 (commit 517f1cfaa); auto-trigger deferred**
- papers/bedc/proposals/README.md shipped (lifecycle + format spec)
- papers/bedc/scripts/prompts/phase_propose.txt shipped (codex prompt v1.0)
- lean4/scripts/review_proposals.py shipped (list / show / accept / reject CLI)
- 用户约束: 不动 codex_revise.py / codex_formalize.py (避免 orchestrator 重启). 当前 phase_propose 仅手动 codex exec 触发
- Phase 2.5 (auto-trigger via codex_revise.py edit) 推迟到 audit gate 跑稳 1-2 周后
- 如果命中率 < 20%, 暂停 Phase 2, 回 Phase 1 继续观察
- 如果命中率 > 50%, 考虑放开 Phase 2 操作员 review 步骤 (变 fully autonomous)

**Decision Gate (Phase 2 → Phase 3)**:
- codex propose 命中率 > 30% 持续 2 周
- 至少 5-10 个 ai_proposed chapter 已通过 TasteGate 进 obligationClosure 以上
- TasteGate 没有捕捉到 false reject (即真理论但 gate 拒绝)
- TasteGate 没有捕捉到 false negative (即 chapter 过 gate 但后期发现是假理论)

## Phase 3 — 长期监控 + 调优 (持续)

**目标**: TasteGate framework 自我演进, 接口在使用中校准。

**数据收集**:

```
lean4/scripts/taste_gate_metrics.py                    新建
  ├── 每个 ai_proposed chapter 的 4 obligation 通过率
  ├── 通过 TasteGate 但后期被发现 "假理论" 的案例 (false negative)
  └── 通不过 TasteGate 但实际是真理论的案例 (false reject, 操作员
      可手动 override 时记录)
```

**接口校准**:
- false negative > 0 → 加约束 (新 obligation 字段)
- false reject > 0 → 放约束 (放宽某条 witness 的 strength)
- 校准频率: 每月一次

**meta-discovery (Tier 3, 长远)**:

```
papers/bedc/scripts/prompts/phase_meta_discover.txt    新建
  └── codex 扫已 mature 的 ai_proposed chapter 集合, 发现 cross-cutting
      pattern (如"这 7 个 chapter 都用了 finite cover ledger"), propose
      capstone-level abstract chapter 抓住这个 pattern
```

**风险**: 高。容易陷入"虚假抽象"。
**Mitigation**: 暂时不实施, 等 Phase 2 跑 1-2 月后再决定。

## 总体时间线

```
Phase 0 (现在做)              ~1 天     无 active gate, 仅 framework 落地
Phase 1 (PR #50 完整 ship 后)  ~半天    active gate 启用, 仅 ai_proposed
Phase 2 (Phase 1 + 1 周观察)   ~2 天    Tier 2 propose 路径开放
Phase 3 (Phase 2 + 持续)                监控 + 校准 + 长远 meta-discovery
```

**总成本到 Phase 2 完成**: ~3-4 天 active 工作 + 等编译器 ship 的 1-2 周等待时间。

## 与现有体系的兼容性

```
现有 NameCert 5 obligation (chapter-internal):
  source / classifier / pattern / ledger / extension
  ─── 不变, 所有 280+ chapter 继续走这条路径

新增 TasteGate 4 obligation (cross-chapter / cross-layer):
  conservativity / no_hidden_input / round_trip / layer_separation
  ─── 仅 \origin{ai} chapter 强制
  ─── \origin{human} 默认不要求

两者 orthogonal:
  - 一个 chapter 可以仅有 NameCert (现有 human-curated)
  - 一个 chapter 也可以同时有 NameCert + TasteGate (ai_proposed)
  - TasteGate 不替代 NameCert; NameCert 不替代 TasteGate
```

## Decision Tree

```
Phase 0 完成?
├── 是 → Phase 1 (等 PR #50 ship)
└── 否 → 继续 Phase 0 直到 reference instance 全过

PR #50 完整 ship?
├── 是 → Phase 1
└── 否 → 继续等 (或在 60% 上做 Phase 0 不阻塞)

Phase 1 完成 + 1 周稳定?
├── 是 → Phase 2 (开放 Tier 2)
└── 否 → 继续观察 Phase 1, 调 audit 规则

Phase 2 命中率 > 30% 持续 2 周?
├── 是 → Phase 3 (长期监控)
└── 否 → 调 phase_propose prompt, 可能回 Phase 1 等待

Phase 3 数据稳定?
├── 是 → 考虑 Tier 3 meta-discovery
└── 否 → 持续校准接口
```

## 备注

- 文档随实施进度更新, 不创建版本号 (按 BEDC 写作纪律, 当前态形式呈现)
- 每完成一个 Phase, 在本文档对应 section 加一个 "Status: completed YYYY-MM-DD" 行
- 如果某 Phase 决定 abandon, 在该 section 加 "Status: abandoned YYYY-MM-DD, reason: ..."
- TasteGate framework 本身不进入 closurestatus 系统 (它是元 framework, 不是 chapter)
