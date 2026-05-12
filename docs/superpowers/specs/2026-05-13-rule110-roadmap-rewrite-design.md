# rule110 路线图重写设计

**日期**: 2026-05-13
**主题**: 重写 `rule110/ROADMAP.md`, 明确实际目标
**作者**: 通过 superpowers:brainstorming 与用户对话产出
**前序**: `2026-05-12-rule110-init-design.md` (rule110 项目初始设计)

---

## 1. 背景与动机

`rule110/ROADMAP.md` 在本次 session 内被多次重写, 产生了一个 7 层"Level"结构 (Level 0-6), 最终目标定为 "bisubstrate-verified BEDC" — 整棵 `lean4/BEDC/` 在 Lean 和 rule110 双 substrate 上 CI 强制一致.

通过对话发现两个 scope drift 问题:

### 问题 1: scope 比用户意图大

用户原指令是 "形式化完所有 `lean4/BEDC/FKernel`". master ROADMAP 的 Level 5/6 把 Derived / BaseReflection / MetaCIC / Capstone 也包进去了, 出 scope. 部分 Beyond-FKernel worker 已经 dispatch (L5.1-L5.6 已 merge, L5.2/L5.7/L5.8 finish 待 merge).

### 问题 2: 框架本身偏离用户原诉求

用户最初的话是:

> "我们这是什么？彻底的构造性数学？"
> "完全二进制不接受任何假设, 来开始分类"
> "我意思我们脱离 CIC"
> "我们可以用 rule110 来做对吧？这是最基础的对么？"

诉求关键词: **彻底构造性、不接受任何假设、脱离 CIC、最基础**.

但实际做出来的是: **rule110 作为 Lean BEDC 的 corroborator** (双 substrate 一致验证), Lean 仍是主 substrate, CIC 仍在信任路径上.

这两件事差别很大. 用户的原诉求更激进 — 想要 BEDC 本身在 rule110 上 self-sufficient.

---

## 2. 元数学澄清

在对话过程中讨论了"能不能真脱离 CIC"这一基础问题, 结论:

### 2.1 任何纯计算 substrate 都识别不了 Π⁰₁

cyclic tag / Rule 110 / 图灵机都是 Σ⁰₁ 计算系统. Π⁰₁ universal quantification (`∀ closed-form X, P(X)`) **不可** universal-replace 到任何 Σ⁰₁ 系统. 这是 Gödel-Tarski 后续元数学的硬定理, 不是工程限制.

### 2.2 CIC 通过 meta-rule 处理 Π⁰₁

CIC 的 induction principle 是 typing rule (元规则), 不是计算. Lean 证 `∀ h: BHist, hsame h h` 时, 内核检查一个有限 term 是否符合 induction eliminator 的类型, **不枚举所有 h**.

这要求信任 CIC 元理论 (induction principle 一致性 + strict positivity).

### 2.3 "CIC 在 rule110 内实现" 不是脱离

把 CIC typechecker 编码成 cyclic-tag 程序 (~10000+ 产生式, 1-3 年工程) **不缩小**信任基:
- 仍然信 CIC 元理论 (induction principle 一致性)
- 加了"CT-encoded CIC typechecker 实现正确"这条新信任 — 而且 CT 程序比 C 代码难审好几个数量级

只是 implementation-level redundancy (catches Lean kernel implementation bugs), 不是 "脱离 CIC".

### 2.4 用户重读: 纯 BEDC 不需要 universal

经讨论, 用户原诉求精确含义不是 "rule110 自足证明 universal", 而是:

> **BEDC 的 ontology 是有限可观察. Lean 的 ∀ 是 syntactic shorthand 帮人类简记, 不是 BEDC 本征所需. 真正的 BEDC content 是 manifest 里逐条具体 assertion.**

这跟"完全二进制不接受任何假设"完全吻合 — BEDC 不需要 universal quantifier 这种 meta-machinery.

### 2.5 推论

- BEDC 验证 = 有限 witness 物理算出, 不需要 universal CT recognizer
- BEDC 验证 = 不需要 CIC-in-rule110 实现
- BEDC trust path 可以**完全脱离 Lean kernel**, 只要每个 closure 的具体 assertion 有 rule110 物理 witness
- Lean 侧 ∀ 陈述保留作为人类阅读 shorthand, 但**不在 BEDC 信任路径上**

---

## 3. 新路线图核心原则

> **BEDC 验证 = 有限 witness, 由 Rule 110 元胞自动机 evolution 物理算出. ANSI C 编译器 + 元胞自动机 evaluator 是信任基. Lean kernel 不在信任路径上.**

### 3.1 信任路径反转

| 维度 | 历史读法 (本 session 大部分时间) | 新读法 (纯 BEDC) |
|---|---|---|
| Substrate 角色 | Lean 主, rule110 corroborator | rule110 主, Lean shorthand |
| BEDC 内容载体 | Lean 里 ∀ 定理 | rule110 manifest assertion |
| 信任基 | Lean kernel + CIC | ANSI C + 元胞自动机 evaluator |
| L4 cross-check 地位 | ship gate | bookkeeping convenience |

### 3.2 BEDC 闭合 (closure) 重新定义

**Closure** = 出现在 `rule110/manifests/<module>/*.{enum,algo}.ct` 里, 由 cyclic-tag evaluator 跑过的具体 assertion.

每条 closure 是个 (输入 X, 期望 accept/reject Y) 对. 由 rule110 substrate 直接物理验证, **不**通过 Lean.

---

## 4. 双 tier 架构

### 4.1 Tier A: cyclic-tag witness

#### 信任路径

```
ANSI C 编译器
    ↓
evaluator/rule110.c (~50 LOC)     — Rule 110 元胞自动机本身, 不在 Tier A trust path 核心
evaluator/cyclic_tag.c (~80 LOC)  — Tier A primitive: cyclic-tag 计算原语
encoder/groundcompiler_encoding.c (~120 LOC)  — bit ↔ tape 编码
    ↓
manifest_runner: 解析 .ct → 跑 cyclic_tag → 比对 expected
    ↓
manifest assertion PASS/FAIL
```

总信任基 ≈ 250 行 C + 文本 manifest. 人眼可审.

#### Ship 标准

- 每个 FKernel closure 对应 `.enum.ct` 通过 `make test` 验证
- `make -C rule110 test` exit 0
- 0 外部依赖 (只 `<stdio.h>` `<stdlib.h>` `<string.h>` `<stdint.h>` `<assert.h>`)

#### 当前状态

- 13 个 FKernel 模块 `.enum.ct` 全 done (~470 assertions)
- 12 个 FKernel 模块 `.algo.ct` 都 done (bounded; 在新框架下不必要但已有, 保留)
- `make test` exit 0
- **Tier A 几乎已 ship**. 收尾 = STATUS.md 更新 + tag release

#### 局限性 (诚实说)

Tier A 信任 cyclic tag 作为另一个 primitive. cyclic tag 比 Rule 110 元胞自动机抽象 (有产生式, 有状态机). 严格意义"完全二进制不接受任何假设"要求衬底是 Rule 110 元胞自动机本身, 那是 Tier B.

### 4.2 Tier B: Rule 110 物理 witness

#### 信任路径

```
ANSI C 编译器
    ↓
evaluator/rule110.c (~50 LOC)     — 唯一的 substrate primitive
    ↓
Rule 110 元胞自动机 evolution on .r110 initial pattern
    ↓
decode evolution 结果 → 匹配 .ct expected
    ↓
manifest assertion PASS/FAIL
```

总信任基 ≈ 50 行 C + Cook 编码 (.r110 ↔ .ct 协议) + 文本 manifest.

#### Ship 标准

- 每个 `.enum.ct` 有对应 `.r110`
- Rule 110 evolution 在 `.r110` 上跑出来 decode 后 = `.ct` 跑出来
- `cyclic_tag.c` 退化为 reference implementation (验证 Cook 编码协议的正确性), **不在 trust path**

#### 当前状态

- L3.1 glider A `(f1_1)=111110` phase-exact ✓
- L3.2 collision A-A 验证 ✓
- L3.3 leader/ossifier/data_block phase-exact entry points + structural docs ✓ (bodies blocked)
- L3.4 cook_encode interface + composition design ✓ (待 merge)
- **L3.1 B-H gliders blocked on Cook 2004 figure access**
- L3.5-L3.7 (.r110 manifest 生成 + round-trip + smoke test) 全 blocked

#### 阻塞分析

Tier B 真正 ship blocker 只有一个: Cook 2004 phase-exact catalog 完整化. 公开二手源不一致, 需要:
- 直接访问 Cook 2004 paper figures, 或
- 找到可信机读 catalog 替代

解锁后预估 4-8 周可完成 L3 全集.

否则 Tier B **无限期 blocked**, Tier A 是当前 deliverable.

---

## 5. Lean / L4 / L5 重新定位

### 5.1 Lean (`lean4/BEDC/FKernel/*`)

- **保留**: 0-axiom 0-sorry 状态不动
- **新地位**: 人类可读的 syntactic shorthand + 论文 bookkeeping
- **不在信任路径**: 任何 Lean kernel bug 不影响 BEDC trust
- **∀ 陈述含义**: 看作"对所有 manifest 列出的具体实例都成立"的紧凑写法, 不是独立逻辑陈述

### 5.2 L4 cross-check 基础设施

- `lean4/scripts/rule110_cross_check.lean` meta-program: 保留
- `lake exe rule110-cross-check`: 保留
- `pr-gate.yml` CI 集成: 保留
- **新地位**: implementation-level cross-check, sanity-check Lean shorthand 和 rule110 witness 是否同步. 不是 BEDC ship gate.
- L4.3 全 13 enum 族扩展 worker 待 merge — **仍然 merge**, 但作为开发期工具

### 5.3 L5 Beyond-FKernel mirrors

- L5.1 TopologyUp / L5.3 CircleUp / L5.4 FoldUp / L5.5 BaseReflection design / L5.6 MetaCIC: **已 merge**, 保留作为 exploratory 附录
- L5.2 RealUp / L5.8 Capstones: finish 但未 merge, 决定**不 merge** (out-of-scope)
- L5.7 GroundCompiler: finish 待 merge, **实际在 scope 内** (encoding primitive), **merge**
- L3.4 Cook encoder interface: finish 待 merge, **merge** (Tier B 工作)

### 5.4 一句话总结

Lean / L4 / L5 已存在工作**不删除**, 但**重新定位**为开发期工具或附录, 不是 BEDC trust 的一部分.

---

## 6. 明确 out-of-scope

下列项**显式不追求**, 不进 ROADMAP 待办列表:

- ❌ Universal CT recognizers (BEDC 不需要 universal — CIC sugar)
- ❌ CIC-in-rule110 实现 (重新引入 CIC 信任)
- ❌ BaseReflection rule110 manifest implementation (研究开放, 也不需要)
- ❌ MetaCIC universal (同上)
- ❌ Beyond-FKernel modules 的 formal closure 主张 (Derived/TopologyUp 等不在 BEDC kernel)
- ❌ L2.1 BHist universal CT recognizer (1-2 月工程, 但不需要 — 见 §6 解释)

### 6.1 为什么不做 universal CT recognizer

纯 BEDC 不需要 universal. 已有的 12 个 `.algo.ct` bounded recognizer 是 session 早期未澄清前 dispatch 的产物, 保留但不维护. ROADMAP **不**列"提升到 universal"作为目标.

### 6.2 为什么不做 CIC-in-rule110

会重新引入 CIC 元理论信任, 还增加"CT-encoded CIC typechecker 正确"这条额外信任. 信任基**变大**不变小. 跟用户原诉求方向相反.

---

## 7. ROADMAP 文件结构 (实际产出)

新 `rule110/ROADMAP.md` 主要章节:

```
1. 项目元信息 (项目名, 分支, 信任约束)
2. 最终目标 (Tier B 严格目标 + Tier A 当前 ship 标准)
3. 核心原则 (BEDC = finite witness; Lean kernel 不在 trust path)
4. 双 tier 架构
   4.1 Tier A: cyclic-tag witness (当前 ship 状态)
   4.2 Tier B: Rule 110 物理 witness (终极目标, blocked on Cook figure access)
5. 当前状态快照 (按 closure 列, 不按 Level)
6. Tier A 收尾步骤 (1-3 天清尾)
7. Tier B 推进步骤 (blocked 工作 + 解锁条件)
8. Lean / L4 / L5 重新定位说明
9. 显式 out-of-scope 列表 (含 universal CT recognizer 不追求的理由)
10. Beyond-FKernel exploratory mirrors 附录 (L5.* 产物)
11. 历史 (m2/m3/master roadmap v1/v2/v3 演变)
12. 给 codex worker 的指令 (autonomous progression)
```

总长度预估 ~200 行 (跟当前 ROADMAP 量级相当, 但内容彻底重组).

---

## 8. 验收标准

### 8.1 文档层面 (路线图自身)

- `rule110/ROADMAP.md` 反映本设计 §3-§6 全部要点
- 任何陈述都是当前态描述 (没有"曾经", "v1", "后来" 之类迭代叙事)
- 无未解释的术语 (Tier A / Tier B 在第一次出现处定义)
- 明确写出"什么算 ship", "什么不算 ship"

### 8.2 实施层面 (即时动作)

- L4.3 + L5.7 + L3.4 待 merge worker 按新框架定位处理 (说明在 ROADMAP §5.3)
- L5.2 + L5.8 待 merge worker 显式放弃 (worktree 清理, 不 merge)
- 更新 STATUS.md 反映 Tier A ship 状态
- 不需要 git revert 任何已 merge 内容

### 8.3 验证命令

```bash
cd /Users/auric/newmath/rule110 && make clean && make && make test
# exit 0
```

上一行是 Tier A ship 标准. 已经在通过.

Tier B 验收等 Cook D 轴解锁.

---

## 9. 风险与开放问题

### 9.1 用户可能后悔扔掉 Lean 主 substrate 定位

如果未来用户改主意觉得 "Lean kernel 仍然应该在 BEDC trust path", 路线图要再改一次. 这次改动不删除任何已有 Lean 工作, 只重新定位, 所以**可逆**.

### 9.2 Tier B 永久 blocked 的可能性

如果 Cook 2004 figure 永远拿不到, Tier B 永远 blocked. ROADMAP 必须明说这点, 不假装 Tier B 是 "soon achievable".

### 9.3 学术受众接受度

"BEDC 不需要 universal quantifier" 是个**强主张**, 可能跟既有 BEDC 论文 (`papers/bedc/`) 的某些 universal 陈述风格冲突. 重写路线图本身不强制论文改写, 但二者**长期需要一致**.

具体: 论文里如果有 `∀` 风格的 BEDC 定理陈述, 应当被理解为 "对所有 manifest assertion 都成立" 的简记, 而不是独立 universal 逻辑陈述. 论文是否需要显式标注这点, 是后续讨论.

### 9.4 codex worker 在新框架下的行为

历史 worker prompt 全部按"Level X"格式. 新 codex worker prompt 模板需要重写, 按 Tier A 收尾 + Tier B 解锁条件 + 出 scope 列表组织.

---

## 10. 下一步

通过 superpowers:writing-plans 把本设计转成具体实施计划:

- 实际写新 `rule110/ROADMAP.md` 内容
- 决定 L4.3 / L5.7 / L3.4 待 merge worker 怎么处理
- 决定 L5.2 / L5.8 worktree 清理
- 更新 `rule110/STATUS.md`
- commit + push
