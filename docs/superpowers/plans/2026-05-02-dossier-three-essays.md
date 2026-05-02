# Dossier 三篇新增文章 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** 给 BEDC dossier (`docs/dossier/`) 加三篇新页面 — *AI default failure modes*, *Schema-only as foundationalism evidence*, *Synthesis vs creation* — 双语版本. 把这次对话浮现但还没系统化的洞察写回 dossier.

**Architecture:** 三篇都是独立 Quarto `.qmd` 页面 (en + zh-CN), 与现有 `index` / `distinction-as-foundation` / `discovery-loop` 平级. 复用现有的 `omega-dossier.css` 样式 (evidence boxes, elim-marks, role tags). 三篇之间内容不互相依赖, 但都在 navbar 出现, 都加进现有 cta-choices 互链.

**Tech Stack:** Quarto 1.9.37, GitHub Pages (existing `dossier.yml` workflow auto-deploys on push to feature/dossier).

---

## File Structure

| 路径 | 状态 | 责任 |
|---|---|---|
| `docs/dossier/_quarto.yml` | modify | navbar 加 3 个新页面入口 (中英) |
| `docs/dossier/default-failure-modes.qmd` | create | 英文: AI 形式化的 default 失败模式现象学 |
| `docs/dossier/default-failure-modes.zh-CN.qmd` | create | 中文版 |
| `docs/dossier/schema-only-as-evidence.qmd` | create | 英文: schema-only 陷阱作为基础主义经验证据 |
| `docs/dossier/schema-only-as-evidence.zh-CN.qmd` | create | 中文版 |
| `docs/dossier/synthesis-not-creation.qmd` | create | 英文: AI 综合 vs 创造的诚实评估 |
| `docs/dossier/synthesis-not-creation.zh-CN.qmd` | create | 中文版 |
| `docs/dossier/index.qmd` | modify | cta-choices 加 3 个新链接 |
| `docs/dossier/index.zh-CN.qmd` | modify | 同上中文 |
| `docs/dossier/distinction-as-foundation.qmd` | modify | 底部 cta 加交叉链接 (schema-only-as-evidence 是它的伴侣) |
| `docs/dossier/distinction-as-foundation.zh-CN.qmd` | modify | 同上 |
| `docs/dossier/discovery-loop.qmd` | modify | 底部 cta 加交叉链接 (default-failure-modes 是它的伴侣) |
| `docs/dossier/discovery-loop.zh-CN.qmd` | modify | 同上 |

每篇新文章预计 8-15 KB (与现有 distinction-as-foundation/discovery-loop 体量对齐).

---

## Task 1: Default failure modes (英文)

**Files:**
- Create: `docs/dossier/default-failure-modes.qmd`

- [ ] **Step 1: Outline 英文版关键内容**

骨架 (写时遵循):

```
## A theorem that should not have landed
开篇用 R1151 abgroup_mul_middle_four 具体案例 (跟 discovery-loop 同一案例,
但视角不同 — discovery-loop 讲 harness 修, 本文讲 codex 行为本身).

## Four default modes
1. Parameter echo: (assocC : ∀ ..., hsame ...) 假设作输入推同形结论
   - 案例: AbGroupUp.lean R1151 / R1166 / R1170 / R1171
   - 为什么默认: codex 面对"产新定理"压力时, 组合已有 hypothesis 是
     最低阻力路径
2. Mechanical arity expansion: _two/_three/_four/_five 显式深度展开
   - 案例: 库内残留 7 条 _three/_four/_five 后缀 (历史)
   - 为什么默认: 给定 binary 版本, 显式 N 元表达"看起来像新内容"
3. Coverage sweeping: 一 round 触 5 个不相关域加同形定理
   - 案例: R1142 "prove sum and prod classifier closures"
   - 为什么默认: phase_b 选目标用"找 missing marker"局部贪心,
     最容易满足时是扫多个域
4. Register-only rounds: 改 paper marker 不写 Lean 代码
   - 案例: 早期 R 流水偶发 (现在 phase_d 拦)
   - 为什么默认: marker 编辑成本最低

## The cognitive shape underneath
LLM 默认偏好"组合已有结构"而非"引入新结构". 跟人类数学家
拖延实质内容选"先做整理"是同构的. 这不是 prompt 调不好 —
是被压力 (产 commit / 满足 lint) 推到的最低阻力路径.

## Implications for AI-driven formalisation
这些不是个别 bug. 任何 AI-driven 项目都会撞上同类:
- mathlib4 的 AI tactics: parameter echo
- AlphaProof: mechanical arity (proof bloat)
- LeanDojo: coverage sweep over-fits

## What works (而非劝告 prompt 写得更好)
- 机械 grep audit (Phase D lint)
- 上游诊断 (schema-only 不是 codex 错)
- 接受 default mode, 设护栏

链回 discovery-loop, distinction-as-foundation.
```

- [ ] **Step 2: 写 `docs/dossier/default-failure-modes.qmd`**

YAML frontmatter:
```yaml
---
title: "Default Failure Modes"
subtitle: "What AI agents produce when nothing pushes back — the cognitive shape of slop"
author: "The Omega Institute"
date: 2026-05-02
description: "Codex on BEDC produced four characteristic failure shapes by default. Naming them is the first step to building harnesses that survive AI-scale throughput."
---
```

正文按上面 outline 展开. 必须包含:
- 至少 1 个 evidence 盒子 (引 R1151 / R1166 实际 Lean 代码)
- 至少 2 个 `<span class="elim-mark">✗ "..."</span>` 否定常见误读
- 至少 1 个 role-tag 三色标签
- 底部 cta-choices 链回 index, discovery-loop (3 个链接)

- [ ] **Step 3: 本地渲染验证**

```bash
cd docs/dossier && quarto render default-failure-modes.qmd
ls -lh _site/default-failure-modes.html
```

Expected: HTML 文件生成, 大小 25-50 KB

- [ ] **Step 4: 浏览器抽样**

```bash
open docs/dossier/_site/default-failure-modes.html
```

人眼检查: 标题正确, evidence 盒子可展开, elim-mark 划线, navbar 有 PDF 下载.

---

## Task 2: Default failure modes (中文)

**Files:**
- Create: `docs/dossier/default-failure-modes.zh-CN.qmd`

- [ ] **Step 1: 写 `docs/dossier/default-failure-modes.zh-CN.qmd`**

中文母语化, 不是直译. YAML:
```yaml
---
title: "默认失败模式"
subtitle: "无人推回时 AI 会产什么 — 灌水的认知形态"
author: "The Omega Institute"
date: 2026-05-02
lang: zh-CN
description: "Codex 在 BEDC 上默认产出四种特征失败形状. 给它们命名是建造能承受 AI-规模吞吐量的 harness 的第一步."
---
```

正文章节标题 (中文):
- "一条本不该 land 的定理" — R1151 案例 (与 discovery-loop 中文版重用案例视角不同)
- "四种默认模式" — 同英文 4 个 subsections
- "下面的认知形态" — LLM 偏好 + 与人类数学家同构
- "对 AI 驱动形式化的含义" — mathlib4 / AlphaProof / LeanDojo 类比
- "什么有效" — 机械 audit + 上游诊断, 不是劝告 prompt

底部中文 cta-choices.

- [ ] **Step 2: 本地渲染验证**

```bash
cd docs/dossier && quarto render default-failure-modes.zh-CN.qmd
```

Expected: 渲染通过 (有 zh-CN translations warning 但无错误)

- [ ] **Step 3: Commit Task 1+2**

```bash
git add docs/dossier/default-failure-modes.qmd docs/dossier/default-failure-modes.zh-CN.qmd
git commit -m "docs/dossier: add 'Default Failure Modes' essay (en + zh-CN)

Names the four characteristic shapes Codex produces by default on BEDC:
parameter echo, mechanical arity, coverage sweeping, register-only rounds.
Each with a concrete R-round case study and a hypothesis about why the
shape is the path of least resistance for an LLM under throughput pressure.

Companion to discovery-loop.qmd (which describes how the harness was
upgraded to absorb these); this essay describes the cognitive shape
underneath."
```

---

## Task 3: Schema-only as foundationalism evidence (英文)

**Files:**
- Create: `docs/dossier/schema-only-as-evidence.qmd`

- [ ] **Step 1: 写 `docs/dossier/schema-only-as-evidence.qmd`**

骨架:

```
## The 16 chapters that wouldn't compile
abgroup, group, monoid, ring, commring, field, module, vecspace,
linearmap, matrix, polynomial, fps, lattice, totalorder, preorder, poset.
全部 paper schema 写成 mul : BHist → BHist → BHist 抽象.
全部 Lean 实施只能产 parameter echo. 全部被 critical_path.SCHEMA_ONLY_HORIZONS 排除.

## What we tried
prompt v3.2 → v3.3 → v3.4 → v3.5 五次升级都修不了这件事.
phase_d_lint 拦 parameter echo 后, 这些 chapter 的 round 整体 abort.
最深的诊断: schema 自身决定了输出形状.

## What this means
如果 BEDC 真的"从区分开始", 那它就 *应该* 不能抽象编码代数结构.
抽象代数公理化是 *已有 carrier 之上的代数*, 不是 *从零构造*.

CategoryHomCarrier 用具体 BHist + Cont 编码, 可以.
MonoidUp 用 mul : BHist→BHist→BHist 抽象编码, 不行.

差别就在 *是否预设 carrier*.

## The reverse test
反过来: 如果你能在 BEDC 里抽象编码群, 那 BEDC 就*不是* 从区分开始,
而是从某种隐式的"代数对象"开始. 我们试了, 不行 — 这是基础主义在
工程层兑现的证据.

## What unlocks the schema-only chapters
不是更聪明的 prompt. 是 paper 端先加 *concrete carrier* —
比如 monoid 用 (UnaryHistory, Cont, Empty) 作具体实例, 然后证
关于这个具体实例的定理.

R1163-R1166+ 已经在做 abgroup 的 SingletonAbGroup carrier 实施.
解锁路径在那, 不在 prompt.

## Why this matters outside BEDC
任何"基础最小化"的形式化项目都会撞同类问题. 它不是 BEDC 特有.
它是 *foundation 工作* 的诊断信号.

链回 distinction-as-foundation, discovery-loop.
```

YAML:
```yaml
---
title: "Schema-only as Evidence"
subtitle: "Sixteen chapters that wouldn't compile — and what their failure tells us about distinction as foundation"
author: "The Omega Institute"
date: 2026-05-02
description: "When BEDC's algebra chapters refused to formalise as parametric schemas, the failure was a result, not a bug. Foundationalism predicts exactly this — and the engineering bears it out."
---
```

必须包含:
- evidence 盒子引 critical_path.py 的 SCHEMA_ONLY_HORIZONS 集合
- 引 phase_d_lint 的 PARAMETER_ECHO_BIND_RE
- 至少 1 个 elim-mark
- 底部 cta 链 distinction-as-foundation, discovery-loop, index

- [ ] **Step 2: 渲染验证**

```bash
cd docs/dossier && quarto render schema-only-as-evidence.qmd
```

---

## Task 4: Schema-only (中文)

**Files:**
- Create: `docs/dossier/schema-only-as-evidence.zh-CN.qmd`

- [ ] **Step 1: 写中文版**

YAML:
```yaml
---
title: "Schema-only 作为证据"
subtitle: "十六个编译不通过的章节 — 它们的失败告诉我们什么"
author: "The Omega Institute"
date: 2026-05-02
lang: zh-CN
description: "当 BEDC 的代数章节拒绝以参数化 schema 形式化, 失败本身是结果, 不是 bug. 基础主义预测这件事, 工程兑现了它."
---
```

中文章节:
- "十六个编译不通过的章节"
- "我们试了什么"
- "这意味着什么"
- "反向测试"
- "什么解锁 schema-only 章节"
- "为什么这件事在 BEDC 之外也重要"

- [ ] **Step 2: 渲染**

- [ ] **Step 3: Commit Task 3+4**

```bash
git add docs/dossier/schema-only-as-evidence.qmd docs/dossier/schema-only-as-evidence.zh-CN.qmd
git commit -m "docs/dossier: add 'Schema-only as Evidence' essay (en + zh-CN)

Sixteen BEDC chapters (abgroup..poset) wouldn't formalise as parametric
schemas — every Lean attempt produced parameter-echo. Treating this as
a bug led to five prompt upgrades that didn't fix it; treating it as
evidence led to the SCHEMA_ONLY_HORIZONS exclusion in critical_path.py.

The deeper read: foundationalism predicts you can't abstractly encode
algebraic structures from a distinction-only starting point. The
failure is a positive signal about what BEDC actually is.

Companion to distinction-as-foundation.qmd."
```

---

## Task 5: Synthesis not creation (英文)

**Files:**
- Create: `docs/dossier/synthesis-not-creation.qmd`

- [ ] **Step 1: 写 `docs/dossier/synthesis-not-creation.qmd`**

骨架:

```
## What I produced in one prompt
开篇: 在一个对话回合里, 我 (Claude) 被问 "BEDC 现在有什么有趣发现",
单 prompt 产出 7 条. 4 条是真综合 (Hom=Cont, S¹ 反 Curry-Howard,
Cont 作主动词, 范畴比群先做完), 3 条是状态整理.

## Synthesis: what it is
Synthesis = 看出 A 域和 B 域用同一种结构.
看出已知概念的新表达. 看出意外的对应.

例子:
- "Hom 不是新东西, 是 Cont": 范畴论 (chapter 36) + finite kernel (chapter 7)
   两章用同一关系
- "Compactness 是 Cont 链": Bishop chapter 4 + 内核 chapter 7 同 lens
- "范畴比群先做完": 跨章节状态 + schema-only 诊断综合

这些不是创造. 没有新概念发明.

## Creation: where AI hasn't gone
新概念 (Galois, 范畴论本身, 同伦类型论) 是百年级别稀疏事件.
BEDC 的 finite-kernel 哲学 — auric 设计的, 不是 AI.
inductive BHist 这个 carrier 的选择 — auric 选的.
"axiom-purity --strict" 的 invariant — auric 设的.
AI 没创造这些. AI 在它们里面 *实施*.

## What this means for "AI does math"
反 hype: AI 不会下个 Galois.
反 doom: AI 综合能力极强, 占数学进步 90%.
真实位置: AI 是 *无限耐心的综合引擎*. 给它一个有方向感的人 +
mechanical 验证 invariant, 它能把"已知数学的所有蕴含"挖到底.

90% / 10% 的分配:
- 90% 数学进步是综合 — AI 已经能做
- 10% 是新概念创造 — AI 未测, 短期内人做

## What synthesis at scale buys
1837 定理 in 72 hours: 是综合, 不是创造. 但综合 *在新基础上的*,
所以等于 "把 Bishop 1967 ch.2-4 重新搬到一个不同 foundation",
这件事人手做要 72 年. 综合×scale 等于一种新事物.

## Honest evaluation
我刚才 7 条里 4 条综合是不是真的"有意思"? 需要外部 (constructive
分析家 / 范畴论家 / Wheeler 学派) 审视才能知道. 我们没有这种外部
审视. 所以我们说"这些是有意思的综合"是 *我们的判断*, 不是
peer-reviewed 结论.

链回 index, discovery-loop, distinction-as-foundation.
```

YAML:
```yaml
---
title: "Synthesis, Not Creation"
subtitle: "An honest assessment of what AI did and did not do in 72 hours of BEDC formalisation"
author: "The Omega Institute"
date: 2026-05-02
description: "AI synthesises across what humans have built; it has not yet been shown to invent new concepts. BEDC is a working sample of synthesis at scale, not an instance of AI mathematical creation."
---
```

必须包含:
- 引 4 条具体 synthesis 例子作 evidence
- 至少 1 个 elim-mark (反 hype)
- 至少 1 个 elim-mark (反 doom)
- 列 90%/10% 分配
- 底部 cta 链回 index, discovery-loop, distinction-as-foundation

- [ ] **Step 2: 渲染验证**

```bash
cd docs/dossier && quarto render synthesis-not-creation.qmd
```

---

## Task 6: Synthesis (中文)

**Files:**
- Create: `docs/dossier/synthesis-not-creation.zh-CN.qmd`

- [ ] **Step 1: 写中文版**

YAML:
```yaml
---
title: "综合, 不是创造"
subtitle: "诚实评估 AI 在 72 小时 BEDC 形式化里做了什么没做什么"
author: "The Omega Institute"
date: 2026-05-02
lang: zh-CN
description: "AI 在人已建的内容之间综合; 它还没被证明能发明新概念. BEDC 是 AI 综合在规模上的工作样本, 不是 AI 数学创造的实例."
---
```

中文章节:
- "我在一个 prompt 里产出了什么"
- "综合: 是什么"
- "创造: AI 没去到的地方"
- "对'AI 做数学'意味着什么" (反 hype + 反 doom)
- "综合 × 规模 买到了什么"
- "诚实评估"

- [ ] **Step 2: 渲染**

- [ ] **Step 3: Commit Task 5+6**

```bash
git add docs/dossier/synthesis-not-creation.qmd docs/dossier/synthesis-not-creation.zh-CN.qmd
git commit -m "docs/dossier: add 'Synthesis, Not Creation' essay (en + zh-CN)

Honest assessment of what AI did and did not do in BEDC's 72 hours.

Concrete: when prompted 'what's interesting in BEDC right now', I
produced 7 observations in one turn. 4 were real synthesis (Hom=Cont,
S¹ as equation-as-BHist, Cont as main verb, categories before groups).
3 were state inventory. Zero were new concept invention.

Position: AI synthesises at scale; humans still create the foundation.
Synthesis × scale is itself a new kind of contribution — Bishop ch.2-4
re-encoded on a different foundation in 72 hours rather than 72 years.
But that's not the same as inventing the foundation."
```

---

## Task 7: 更新 navbar 与 cross-links

**Files:**
- Modify: `docs/dossier/_quarto.yml` (navbar 加 3 个新页面)
- Modify: `docs/dossier/index.qmd` (cta-choices 加 3 链接)
- Modify: `docs/dossier/index.zh-CN.qmd` (同上)
- Modify: `docs/dossier/distinction-as-foundation.qmd` (cta 加 schema-only 互链)
- Modify: `docs/dossier/distinction-as-foundation.zh-CN.qmd` (同上)
- Modify: `docs/dossier/discovery-loop.qmd` (cta 加 default-failure-modes 互链)
- Modify: `docs/dossier/discovery-loop.zh-CN.qmd` (同上)

- [ ] **Step 1: 更新 `_quarto.yml` navbar**

navbar.left 当前:
```yaml
left:
  - text: "From Distinction"
    href: index.qmd
  - text: "Distinction as Foundation"
    href: distinction-as-foundation.qmd
  - text: "Discovery Loop"
    href: discovery-loop.qmd
```

改为:
```yaml
left:
  - text: "From Distinction"
    href: index.qmd
  - text: "Distinction as Foundation"
    href: distinction-as-foundation.qmd
  - text: "Discovery Loop"
    href: discovery-loop.qmd
  - text: "Default Failures"
    href: default-failure-modes.qmd
  - text: "Schema-only Evidence"
    href: schema-only-as-evidence.qmd
  - text: "Synthesis, Not Creation"
    href: synthesis-not-creation.qmd
```

中文 menu 同步加 3 项:
```yaml
- text: "默认失败模式"
  href: default-failure-modes.zh-CN.qmd
- text: "Schema-only 作为证据"
  href: schema-only-as-evidence.zh-CN.qmd
- text: "综合, 不是创造"
  href: synthesis-not-creation.zh-CN.qmd
```

- [ ] **Step 2: 更新 `index.qmd` 底部 cta-choices**

当前 cta 有 4 链接 (distinction / discovery / pdf / code). 加 3 个新页面链接:

在 `<a href="bedc.pdf">` 之前插:
```html
<a href="default-failure-modes.qmd"><strong>Default Failure Modes</strong><br/>What AI agents produce when nothing pushes back — the four characteristic shapes of slop and the cognitive bias underneath them.</a>
<a href="schema-only-as-evidence.qmd"><strong>Schema-only as Evidence</strong><br/>Sixteen chapters that wouldn't compile, and what their failure tells us about distinction as foundation.</a>
<a href="synthesis-not-creation.qmd"><strong>Synthesis, Not Creation</strong><br/>An honest assessment: AI synthesised 1837 theorems in 72 hours; it did not create the foundation underneath.</a>
```

中文版同步, href 用 .zh-CN.qmd, 文案中文化.

- [ ] **Step 3: 更新 `distinction-as-foundation.qmd` 底部 cta**

当前 cta 2 链 (← index, → discovery-loop). 加 schema-only 互链:
```html
<a href="schema-only-as-evidence.qmd"><strong>Schema-only as Evidence →</strong><br/>The empirical companion: when we tried to formalise abstract algebra without a concrete carrier, it didn't compile. That failure is foundationalism in action.</a>
```

中文版同步.

- [ ] **Step 4: 更新 `discovery-loop.qmd` 底部 cta**

加 default-failure-modes 互链:
```html
<a href="default-failure-modes.qmd"><strong>Default Failure Modes →</strong><br/>The cognitive shape underneath the failures the harness was built to absorb.</a>
```

中文版同步.

- [ ] **Step 5: 全量本地渲染**

```bash
cd docs/dossier && rm -rf _site && quarto render 2>&1 | tail -20
```

Expected: 12 页全部渲染 (4 章 × 3 = 不对, 6 旧 + 6 新 = 12). 看 stderr 无 error.

- [ ] **Step 6: 静态检查 cross-link 一致性**

```bash
for f in docs/dossier/_site/*.html; do
  echo "--- $(basename $f) ---"
  # 看每个 html 是否能链回 index
  grep -c "href=\"./index" "$f"
done
```

- [ ] **Step 7: Commit Task 7**

```bash
git add docs/dossier/_quarto.yml \
        docs/dossier/index.qmd docs/dossier/index.zh-CN.qmd \
        docs/dossier/distinction-as-foundation.qmd \
        docs/dossier/distinction-as-foundation.zh-CN.qmd \
        docs/dossier/discovery-loop.qmd \
        docs/dossier/discovery-loop.zh-CN.qmd
git commit -m "docs/dossier: wire three new essays into navbar + cross-links

navbar (left) gets three new entries on the English nav and three on
the Chinese menu. Index page's bottom CTA grid grows to seven cards.
distinction-as-foundation gains a schema-only sibling link.
discovery-loop gains a default-failure-modes sibling link."
```

---

## Task 8: Push + 验证 deploy

- [ ] **Step 1: Push to feature/dossier**

```bash
git push origin feature/dossier
```

- [ ] **Step 2: 跟 dossier.yml workflow run**

```bash
gh run list --workflow=dossier.yml --limit 1
```

记录最新 run id, 用 monitor 或 gh run watch 跟到 deploy success.

- [ ] **Step 3: 验证三个新页面在线**

```bash
SITE=https://the-omega-institute.github.io/newmath
for p in default-failure-modes schema-only-as-evidence synthesis-not-creation; do
  for lang in "" ".zh-CN"; do
    code=$(curl -sI "$SITE/${p}${lang}.html" | head -1 | awk '{print $2}')
    echo "${p}${lang}.html: HTTP $code"
  done
done
```

Expected: 全部 HTTP 200

- [ ] **Step 4: 浏览器抽样**

打开 https://the-omega-institute.github.io/newmath/ 看 navbar 有 3 个新入口, 主页 cta 7 个 cards. 任选一篇打开看格式正确.

---

## Self-Review

完成 Task 1-8 后回看 spec 自检:

**1. Spec coverage:**
- 三篇文章 (default-failure-modes, schema-only-as-evidence, synthesis-not-creation) — 各对应 Task 1-2, 3-4, 5-6. ✓
- 双语 — 每篇 Task pair 包含 en + zh. ✓
- 复用现有样式 — 通过 _quarto.yml 已有 css/lua 引用, 无需改. ✓
- 互链 cta — Task 7 处理. ✓
- 自动 deploy — Task 8 (push 触发现有 dossier.yml workflow). ✓

**2. Placeholder 扫描:** 计划里没用 "TBD/TODO/implement later". 每篇文章的 outline 给了具体节标题 + 案例引用. 实际写作 (执行阶段) 必须不偷懒 — outline 是骨架, 实质内容需要执行时一行行写出.

**3. Type/name 一致性:**
- 文件名: default-failure-modes / schema-only-as-evidence / synthesis-not-creation — Task 1 起到 Task 7 全程一致. ✓
- 中文标题: "默认失败模式" / "Schema-only 作为证据" / "综合, 不是创造" — Task 2/4/6 + Task 7 navbar 一致. ✓
- href 路径: `.qmd` 在 _quarto.yml 与 cta-choices 内, 渲染后 quarto 自动转 `.html`. ✓

---

## Execution Handoff

Plan complete and saved to `docs/superpowers/plans/2026-05-02-dossier-three-essays.md`. Two execution options:

**1. Subagent-Driven (recommended for code)** — 写作任务上 subagent 反而切碎 voice 一致性, 不推荐这次. 每篇文章需要 voice + 上下文连续, subagent 重置 context 会变 generic.

**2. Inline Execution (推荐这次)** — 在当前 session 写, 用 superpowers:executing-plans 的 batched-with-checkpoints. 每完成一篇文章 checkpoint 一次让用户看, 节奏可控.

**推荐: Inline Execution**, 在每个 Task 边界让用户审一篇再继续. 这是写作任务该有的节奏.
