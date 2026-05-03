# 工作规范

## 环境与工具链

- Python: 使用 `python3` (stdlib only, 工具脚本无第三方依赖)
- LaTeX: 使用 `pdflatex`(BEDC 论文体内零中文; 顶层 README/CLAUDE/AGENTS 用中文但不进入 PDF)
- Lean 4: `lake build`; `lean4/` 为 **mathlib-free** 形式化, 从 first principles 起步
- 单个 `.tex` 文件不超过 800 行, 超过须拆分
- 二进制运算使用原生实现, 不用二进制字符串

## 语言与格式

- 工作语言默认中文, 英文版文档以 `_en.md` / `_en.tex` 结尾
- 数学公式只用 `$` 与 `$$`; `$$` 必须独立成行

## 写作纪律

- **禁止任何迭代叙事**: 不出现"新增""修订""修复了上一版本""v1.5.X 增量""patch""migration""frozen""supersede""increment""legacy"等字样
- 论文以**完整当前态**形式呈现; 理论扩展在原章节内追加, 不留版本号痕迹
- 不生成修改记录、日志、总结、变更原因、报告
- 不添加文件内备注
- 有问题直接改, 无需备份

## 项目结构

- `lean4/` — Lean 4 形式化, mathlib-free, 0 axiom 0 sorry
- `papers/bedc/` — BEDC LaTeX 论文 (现行态)
- `papers/bedc/parts/project_governance/theory_amendment_policy.tex` — 持续发展规则
- `papers/bedc/parts/project_governance/HOW_INCREMENT_WORKS.md` — 增量配方
- `lean4/scripts/bedc_ci.py` — paper-Lean drift 审计 (`\leanchecked{X}` X 必须真存在)
- `tools/check-axioms.py` — axiom 禁用审计脚本 (CI gate)

---

# Lean 4 形式化纪律

## I. mathlib-free first-principles

- `lean4/lakefile.lean` 不得含 `require ... mathlib ...`
- 证明只使用 Lean 4 stdlib + 内置战术 (`exact` `intro` `cases` `rfl` `simp` `induction` `decide` `apply` `constructor`)
- 不得引入 `import Mathlib.X.Y` 或任何 mathlib 衍生包

## II. 完全禁止 axiom

**BEDC 项目硬 invariant: `lean4/BEDC/` 任何位置不得出现 `axiom` 关键字。**

所有"原始对象"必须用以下方式编码:

- **闭生成类型** → `inductive` (BMark / BHist / ProbeBundle / SigRel / psame)
- **可定义谓词或函数** → `def` (msame / hsame / Ext / Cont / InGapSig / InBundle)
- **抽象 carrier** → `class`/`structure` 字段 (AskSetup / PackageSetup / DomainSetup / NameCertSetup / BaseReflectionSetup)

如果你正想写 `axiom`, **停下**, 改用以下决策树:

1. 这是闭生成类型(有限构造子)? → 写 `inductive`
2. 这是从已有结构能推导出来的谓词或函数? → 写 `def`
3. 这是真正抽象的 carrier (实现可选)? → 加到对应的 `*Setup` class/structure 字段
4. 都不适用? **重新设计接口, 不允许加 axiom**.

理论 invariant: BEDC 形式化等价于"基于 Lean 4 Calculus of Inductive Constructions 的纯证明", 没有任何额外的逻辑承诺. 引入新 axiom 会破坏这个 invariant.

## III. 审计与 CI gate

- `tools/check-axioms.py` 强制执行: 任何 `axiom` 声明会让脚本 exit 1
- `.github/workflows/lake-build.yml` 跑 `python3 tools/check-axioms.py`; PR 中如出现 axiom, CI 拒绝合并
- 不接受"先注册再说"或"加 allowlist"的工作流; 这是项目级 invariant, 不是可调阈值

## IV. 0 sorry 不变量

- 当前所有 public theorem 都是真证明; 不得写新 `sorry` 占位
- 如确实暂无证明, 用 `theorem T : True := True.intro` 占位 + `-- TODO:` 注释 (不污染审计)
- 或者改写定理形式让证明在闭生成结构上自然成立

## V. typeclass 设计纪律

- 4 个 setup class 各自只放真正所属的字段 (AskSetup 不得放 Pkg)
- 提供 `Minimal*Setup` 实例 (`Unit` 类型 + 平凡谓词) 让 Examples/ 与下游使用
- BaseReflectionSetup 是 `structure` 不是 `class`, 与 FKernel 独立, 不共享类型

---

# 论文 ↔ Lean 验证状态联动

## 状态宏 (preamble.tex)

每个论文中讨论的 Lean 目标用对应宏标注其当前状态:

- `\leanchecked{Lean.Target.name}` — 该 paper site 的 canonical 主实现 (绿 ✓), 每 paper site 只一条
- `\leanvariant{Lean.Target.name}` — 同一 paper claim 的 wrapper / projection / 不同 binder 风格 / 弱化结论等变体 (灰小字, `↪ variant` 缩进), 每 primary 下可多条
- `\leansorryd{Lean.Target.name}{rationale}` — 暂用 sorry (橙) -- 项目 invariant 是 0 sorry, 此宏用于未来如有重新出现
- `\leanstmt{Lean.Target.name}` — statement-only / structure 字段 (蓝)
- `\leandef{Lean.Target.name}` — `def` 或 `inductive` 定义 (灰)

## 下划线规则

- 调用时 underscore 必须写成 `\_` (LaTeX 转义), 例如:
  ```latex
  \leanchecked{BEDC.BaseReflection.PackageReflection\_base}
  ```
- `xstring` 把 `\_` 替换为细空格, PDF 中不显示字面下划线
- 命名空间 `.` 保持字面

## marker 使用纪律

- 每个 Lean 目标在论文中**只标注一次**(primary site, 即定理首次形式化处)
- 每个 paper 定理点**最多一条 `\leanchecked`** (canonical 主实现); 同 claim 的 wrapper / projection / 不同 binder 风格 / 弱化结论用 `\leanvariant` 标注
- `papers/bedc/parts/proof_obligations/lean_scaffold_contract.tex §41.4` 是例外: 5 个 base-reflection 目标的"一站式"摘要块
- 状态变化时 (sorry → checked, def → checked) 同一 commit 更新 marker; `bedc_ci.py audit` 强制所有 `\leanchecked` / `\leanvariant` 的 X 在 Lean 真存在

---

# 持续发展规则

## 理论扩展

- 新增定义、定理、谓词: 在对应主题章节内**就地追加**
- 替换旧表述: **删旧加新**, 不留废弃段落 / 不写"deprecated"标注
- 见 `papers/bedc/parts/project_governance/theory_amendment_policy.tex`

## 增量配方

新增一个理论增量 (新定理或新概念) 的标准流程见 `HOW_INCREMENT_WORKS.md`:

1. 把新章节追加到对应 `papers/bedc/parts/<theme>/` 目录
2. 在 `lean4/BEDC/...` 添加对应 Lean 目标 (`def` / `theorem` / 新增 inductive 构造子)
3. 在论文章节调用对应 `\leanchecked` 系列宏
4. `lake build` + `make` + `check-axioms.py` + `bedc_ci.py audit` 四过

## label 命名

- chapter `\label{ch:<theme>-<concept>}` (semantic, 不含版本号)
- section `\label{sec:<theme>-<concept>}`
- theorem `\label{thm:<concept>}`, definition `\label{def:<concept>}`, principle `\label{prin:<concept>}`, etc.
- **禁止**包含 `vNNN-`, `v1.5.X`, `v14-` 等版本前缀

---

# 构建与审计

## 完整本地验证

```bash
cd lean4 && lake build                            # 0 axiom, 0 sorry, build OK
cd papers/bedc && make                            # pdflatex 双趟, 130+ 页 PDF
python3 tools/check-axioms.py                     # 源代码 axiom 禁用审计
python3 lean4/scripts/bedc_ci.py audit            # paper ↔ Lean drift 审计
python3 lean4/scripts/bedc_ci.py axiom-purity     # 传递依赖审计 (禁 Classical.choice / Quot.sound)
```

五项全 exit 0 才算 ship 标准.

`axiom-purity --strict` 用 `#print axioms` 检测每条 BEDC 定理的传递依赖, 强制零 Lean stdlib 公理依赖: 禁 `Classical.choice` (LEM/选择公理)、`Quot.sound` (商类型公理) 和 `propext` (命题外延). BEDC 现状: 562 个定理全部纯 CIC 派生, 不依赖任何 stdlib 公理, 跟 Brouwer / Bishop 严格 constructive 同档.

## CI

`.github/workflows/lake-build.yml` 在 `lean4/**` 或 `tools/check-axioms.py` 改动时触发:

1. `cd lean4 && lake build`
2. `python3 tools/check-axioms.py`

任一失败 PR 不可合并.

---

# Codex pipeline 协作纪律

`codex-auto-dev` 分支上常驻并行 codex worker (`lean4/scripts/codex_formalize.py` + `papers/bedc/scripts/codex_revise.py`), 每个 worker 周期性 fetch + rebase 远端然后 push 自己的小 commit. 人工提交必须按下述纪律, 否则会触发 rebase 风暴.

## HOT 共享文件

下面四个文件所有 worker 都可能修改, 任何提交动到它们都会卡 rebase 队列:

- `papers/bedc/preamble.tex` (worker 加新 `\Up` 宏会动)
- `papers/bedc/main.tex` (worker 加章节 `\input` 会动)
- `papers/bedc/parts/capstones/_index_files.tex`
- 类似 index / dispatch 入口文件

## 提交切分规则

人工提交涉及上述任一 HOT 文件 + N 个新文件时, **必须拆开**:

1. **commit A**: 仅 HOT 文件改动 (新 `\Up` 宏 / 新 `\input` 行 / index 改动). push.
2. 等 30 秒, 让 worker 在你的小改动上完成本轮 rebase.
3. **commit B**: 全部新文件 (新章节 / 新模块). push.

新文件 worker 不会动, 批量提交无冲突风险. 危险只在 HOT 文件多人争抢.

## push 前活跃度检查

```bash
gh run list --branch codex-auto-dev --limit 5
```

若有 ≥ 2 个 `in_progress` run, 等到只剩 0-1 个再 push HOT 文件 commit. 否则 worker 们一窝蜂 rebase 你的 commit, 再加上它们彼此的小 commit, 三角冲突几乎无法自动恢复.

## 同步远端: 三种场景三种做法

**禁止把"落后远端 100+ commit"时直接 `git pull --rebase`** —— 它把每个 codex 小 commit 重新 apply 到你的 local commit 上, 一个冲突让一长串 commit 进入 rebase-conflict 状态. 改用以下决策树:

| 本地状态 | 远端落后 | 做法 |
|---|---|---|
| 只有未 commit 的 working tree 改动 | 任意 | `git stash -u` → `git pull --ff-only origin <branch>` → `git stash pop` |
| 已 commit + 落后少 (< 10) | < 10 | `git pull --rebase origin <branch>` (重写少量 local commit 风险可控) |
| 已 commit + 落后多 (≥ 10) | ≥ 10 | `git fetch origin <branch>` 然后 `git merge origin/<branch>` (生成 merge commit, 不重写任何历史) |

**重点**: 落后远端多且本地有 commit 时, `git merge` 比 rebase 安全得多 —— 远端 codex worker 的 commit 保持原样, 本地 commit 保持原样, 冲突只发生在一个 merge 点. rebase 把每个 codex 小 commit 都拿你的工作重 apply 一遍, 冲突一旦出现就在长链上扩散.

**绝对禁止** `git reset --hard origin/<branch>` 当本地有未推送 commit 时 —— 直接丢工作.

## 历史教训

2026-05-03 RH 路线图提交 (`da6e6e10`, 16 文件 / 2108 行, 含 preamble + main) 触发 codex pipeline rebase 风暴: 30 分钟内 7 个 worker commit 在同一秒落地 (`14:22:35`), 然后三个 fix commit (`693fb128` / `001d0c3d` / `0cdf518c`) 加 PID-lock + abort + codex 兜底才把状态修干净. 那一次本可避免: 把 preamble / main / `_index_files` 改动单独 push, 再 push 13 个新章节文件, 不会触发任何争抢.

---

# The Omega 科研宪章

## I. 第一性原理优先

- 每个结论须能追溯到定义、归纳构造、`class` 字段或已证命题
- 直觉、命名和物理解释不得替代证明
- Lean 与论文中的主张通过 `\leanchecked` 系列宏严格对齐

## II. 最小输入原则

- 优先 `inductive` / `def` / `class`, 而非 `axiom`
- 优先依赖更少、结构更短的表述
- 不为叙事完整引入不可检验的额外结构

## III. 显式依赖链

- 论文 `\leanchecked{X}` 与 Lean 命题对应关系由 `bedc_ci.py audit` 强制 (X 必须在 lean4/BEDC/ 真存在, 否则 audit fail)
- 跨层引用须经 `\autoref{ch:...}` 解析, 不留 dangling
- 论文中的 `\leanchecked` 状态须与 Lean 实现一致 (CI 审计)

## IV. 可证伪与量化约束

- 经验性或数值性主张须附带观测量、误差口径与适用边界
- 纯理论结果须给出至少一种一致性检查: 边界情形、极限行为或已知特例复现
- 负面结果与失败模式须显式记录, 不得用"未来工作"掩盖

## V. 可复现、可审计

- 构建过程必须可复现 (上述 4 命令)
- 生成结果须能回溯到源文件与依赖链
- 任何理论修改同步 paper + Lean + metadata, 三方 CI 一致才能合并

---

# Skill routing

When the user's request matches an available skill, ALWAYS invoke it as the first action.

Key routing rules:

- Brainstorm, product idea, "is this worth building" → `/office-hours`
- Scope, product framing, milestone shaping → `/plan-ceo-review`
- Architecture, technical design, implementation plan → `/plan-eng-review`
- Bugs, errors, regressions, root cause analysis → `/investigate`
- Code review, diff review, pre-merge review → `/review`
- Design system, visual direction → `/design-consultation`
- Visual audit, polish, UI QA → `/design-review`
- Benchmark, performance regression, web vitals → `/benchmark`
- Canary, post-deploy verification, production watch → `/canary`
- Security audit, threat model, OWASP review → `/cso`
- Docs sync after shipping → `/document-release`
- Auto-run full review gauntlet → `/autoplan`
