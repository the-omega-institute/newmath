# 工作规范

## 环境与工具链

- Python: 使用 `python3` (stdlib only, 工具脚本无第三方依赖)
- LaTeX: 使用 `pdflatex`(BEDC 论文体内零中文; 顶层 README/CLAUDE/AGENTS 用中文但不进入 PDF)
- Lean 4: `lake build`; `lean4/` 为 **mathlib-free** 形式化, 从 first principles 起步
- 单个 `.tex` 文件不超过 800 行, 超过须**直接 split** 出 sibling 文件, 把相对独立的子主题搬过去并 `\input` 进来. **禁止用任何"压缩空行 / 删空白行 / 把多行合并成一行"等格式压缩动作来给文件腾空间**: 这类动作不传达任何理论内容, 是 code-debt churn, 也会让 git diff 噪音盖过真正的语义改动. 若 split 不出明显独立的子主题, 报告原因, 不要伪装成靠空行省下来的改动
- **Hub-only 索引文件**: 任何作为 chapter / section 索引的 hub `.tex` 文件 (例如 `\input{...}` 或 `\include{...}` 集中处) 只放结构性元素: 标题宏 (`\chapter` / `\section` / 等) + `\label` + 1-2 句 orienting 段落 + 子文件 `\input{...}` 行 + 必要的状态标注 (如 `\closureat`). **不放任何 `\begin{theorem}` / `\begin{definition}` / `\begin{lemma}` / `\begin{proof}` 等正文环境**. 正文移入同主题子目录的 sibling `.tex` 文件, 文件名按内容 slug 命名 (`<slug>.tex`). hub 自身一般 5-15 行, 始终远低于 800 行上限
- 二进制运算使用原生实现, 不用二进制字符串

## 语言与格式

- 工作语言默认中文, 英文版文档以 `_en.md` / `_en.tex` 结尾

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

- 各 setup class 只放真正所属的字段 (AskSetup 不得放 Pkg)
- 提供 `Minimal*Setup` 实例 (`Unit` 类型 + 平凡谓词) 让 Examples/ 与下游使用
- BaseReflectionSetup 是 `structure` 不是 `class`, 与 FKernel 独立, 不共享类型

---

# 论文 ↔ Lean 验证状态联动

## 状态宏 (preamble.tex)

每个论文中讨论的 Lean 目标在论文里通过两类宏标注：

### Lean 标记宏 (verification 轴 only)

- `\leanchecked{Lean.Target.name}` — 该 paper site 的 canonical 主实现 (绿 ✓), 每 paper site 只一条; 对应 `formalstatus = theoremCheckedV`
- `\leanvariant{Lean.Target.name}` — 同一 paper claim 的 wrapper / projection / 不同 binder 风格 / 弱化结论等变体 (灰小字, `↪ variant` 缩进), 每 primary 下可多条
- `\leansorryd{Lean.Target.name}{rationale}` — 暂用 sorry (橙) -- 项目 invariant 是 0 sorry, 此宏用于未来如有重新出现; 对应 `formalstatus = formalTargetV`
- `\leanstmt{Lean.Target.name}` — statement-only / structure 字段 (蓝); 对应 `formalstatus = formalTargetV`
- `\leandef{Lean.Target.name}` — `def` 或 `inductive` 定义 (灰); 对应 `formalstatus = encodedDefV`

这些宏只描述 Lean-side 验证状态. 它们不暗示 paper 一侧的 closure 等级.

### Closurestatus 块 (theory × verification 两轴)

每个 `<X>Up` 章末尾用 `closurestatus` 环境记录两轴状态:

```latex
\begin{closurestatus}{\<X>Up}
  \theoryclosure{\scopedClosure}      % paper 一侧理论闭合等级
  \scopeclosed{<一句话写清精确闭合范围>}
  \formalstatus{\theoremCheckedV}     % Lean 一侧验证等级
  \leantarget{BEDC.<...>.<theorem>}  % 必须在 lean4/BEDC/ 真存在
  \bridgestatus{none}                 % none / paperBridge / bridgeChecked
  \notclaimed{<一句话: 本章明确不闭合的内容>}
  \upgradepath{<一句话: 升级到下一闭合等级所需补足>}
\end{closurestatus}
```

闭合等级 (理论轴) 取自 `seed | obligation | scopedClosed | publicClosed | bridgedClosed | maturePackageClosed`, 验证等级取自 `unformalized | formalTarget | encodedDef | scaffoldChecked | theoremChecked | auditClean | axiomClean | bridgeChecked`.

两个轴是**独立的**: paper 闭合不依赖 Lean 验证, Lean 验证也不创造 paper 闭合. 二者只通过 `VerifiedGate(N, c, v) := TheoryGate(N, c) ∧ FormalStatus(N, v)` 同时报告.

### 下划线规则

- 调用 `\leanchecked` / `\leantarget` 等时, underscore 必须写成 `\_`, 例如 `BEDC.BaseReflection.PackageReflection\_base`
- `xstring` 把 `\_` 替换为细空格, PDF 中不显示字面下划线
- 命名空间 `.` 保持字面

### marker 使用纪律

- 每个 Lean 目标在论文中**只标注一次**(primary site)
- 每个 paper 定理点**最多一条 `\leanchecked`** (canonical 主实现); 同 claim 的变体用 `\leanvariant` 标注
- `papers/bedc/parts/proof_obligations/lean_scaffold_contract.tex §41.4` 是例外: base-reflection 目标的"一站式"摘要块
- 状态变化时 (sorry → checked, def → checked) 同一 commit 更新 marker; `bedc_ci.py audit` 强制所有 `\leanchecked` / `\leanvariant` / `\leantarget` 的 X 在 Lean 真存在
- **绝不**把 closure 轴写成 verification 轴的函数, 也不要反过来; codex pipeline 的 `axis-confusion` gate 会拒绝这类 round

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
4. 走完上节"完整本地验证"列出的全部命令

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
cd papers/bedc && make                            # pdflatex 双趟, 生成 PDF (~75s)
python3 tools/check-axioms.py                     # 源代码 axiom 禁用审计
python3 lean4/scripts/bedc_ci.py audit            # paper ↔ Lean drift 审计
python3 lean4/scripts/bedc_ci.py axiom-purity     # 传递依赖审计 (禁 Classical.choice / Quot.sound)
```

上述命令全部 exit 0 才算 ship 标准.

## 开发循环: 用 `make check` 代替 `make`

提交 / 出版前用 `make` (双趟, 生成 PDF, 解析 `\autoref` / TOC). 平时反复改章节、试错时用 `make check` —— 单趟 `pdflatex -draftmode`, 大约一半时间 (40s vs 75s), 仍然抓到所有真错误 (Undefined control sequence / Missing $ / Extra } / unresolved `\input` / package errors). 唯一代价: 交叉引用印成 `?? on page ??`, 对开发循环不影响. **不要在 ship 前用 `make check` 替代 `make`**: 你需要看 PDF 真实出来, 也需要确认所有 `\autoref` 解析 (CI 会查).

`axiom-purity --strict` 用 `#print axioms` 检测每条 BEDC 定理的传递依赖, 强制零 Lean stdlib 公理依赖: 禁 `Classical.choice` (LEM/选择公理)、`Quot.sound` (商类型公理) 和 `propext` (命题外延). BEDC 全部定理纯 CIC 派生, 不依赖任何 stdlib 公理, 跟 Brouwer / Bishop 严格 constructive 同档.

## CI

`.github/workflows/lake-build.yml` 在 `lean4/**` 或 `tools/check-axioms.py` 改动时触发:

1. `cd lean4 && lake build`
2. `python3 tools/check-axioms.py`

任一失败 PR 不可合并.

---

# 本机管线 (我们的 pipeline)

本机只跑 `tools/bedc-deep/supervisor.py` (外圈 supervisor + 内圈 `oracle_client.py --loop` + `bedc_oracle_server.py` HTTP :8767), 做 BOARD-driven 论文深度推理 + theorem-site 补全. 跟下面那条 codex-auto-dev 上的 codex_revise.py / codex_formalize.py 闭合追踪管线**完全无关**, 互补但物理隔离.

- 永远不要在本机起 `codex_revise.py` 或 `codex_formalize.py` —— 那是 loning 在 cloud 跑的, 不是我们的
- Lean 一侧本机不跑, 任何"启 lean 提速"的建议都是错的
- 停 supervisor: 写 `tools/bedc-deep/.stop` (sentinel)
- 进程标识: `ps aux | grep -E 'supervisor\.py|oracle_client\.py|bedc_oracle_server'`
- 日志: `tools/bedc-deep/state/supervisor_logs/{supervisor.log,inner.log,...}`
- 状态/产出: BOARD targets 在 `tools/bedc-deep/state/b-NNN_*` 各自 dir, 主板见 `tools/bedc-deep/BOARD.md`
- 模块栈: `auto_discovery.py` (BOARD 补水), `paper_gap_scanner.py`, `prior_art.py`, `paper_index.py`, `dispatch_bedc_target.py`, `board_archive.py`, `pi_agent_v1.py` (PI 周期 review), `dashboard.py`, `loning_watch.py` — 都属 supervisor stack
- 并行: `--codex-parallel N --oracle-parallel M` 双池, default 3+3, oracle 池受 active ChatGPT tab 数 clamp
- "Pipeline 暂停 / 卡了" 一般指 supervisor 进程活着但 (a) BEDC ChatGPT tab 关了 → oracle 队列 `queue_waiting_for_browser_agent` 空转, 或 (b) Stage 2 paper writeback validators (`item_8` / `line_cap` 之类) 反复拒. 看 `state/supervisor_logs/supervisor.log` 模式定位
- loning 改 `papers/bedc/scripts/` / `lean4/scripts/` 的脚本会随 git merge 落地到本仓, 但 supervisor 不消费这些脚本; "整合 loning 的优化" 对我们而言只是 prompt-level 选择性借鉴, 不是 git-level 自动 import
- ~/.claude/projects/.../memory/ 不要再单独建文件保存这些事实, 写到本节即可

---

# Codex pipeline 协作纪律 (loning 的 cloud 管线, 不是我们)

`codex-auto-dev` 分支上常驻并行 codex worker (`lean4/scripts/codex_formalize.py` + `papers/bedc/scripts/codex_revise.py`), 每个 worker 周期性 fetch / rebase 远端然后 push 自己的小 commit.

## 核心规则: 单 commit 原子提交 + merge 不 rebase

**人工提交一律单 commit 原子打包**, 涉及多少文件无所谓. 永远不要把"HOT 文件改动"和"新文件"拆成两个 commit —— 那会让 commit A 在远端处于编译失败的中间状态 (e.g. `_index_files.tex` 引用还没被 push 的章节文件), CI 跑一次失一次, codex worker 拉到那一刻也会 build fail.

每个 commit 必须 *自己就编译干净*. 这是底线, 优先级高于 worker 冲突优化.

## 同步远端: 一律用 git merge, 不用 rebase

push 被拒绝 (远端有新 commit) 时, 不要 `git pull --rebase` 也不要 `git pull` (默认 merge 但行为不显式). 用:

```bash
git fetch origin <branch>
git merge origin/<branch>      # 生成 merge commit, 远端 codex commit 和本地 commit 都保留原样
git push origin <branch>
```

**禁止 `git pull --rebase`** —— 落后远端多个 codex 小 commit 时, rebase 把你的 local commit 在每个 codex commit 上重 apply 一遍, 一个冲突就让一长串 commit 进入 rebase-conflict 状态.

**禁止 `git reset --hard origin/<branch>`** 当本地有未推送 commit 时 —— 直接丢工作.

未 commit 的 working tree 改动, 用 `git stash -u` → `git pull --ff-only origin <branch>` → `git stash pop`. (这个场景也 OK 用 merge, 但 ff-only 更轻.)

## push 前活跃度检查

```bash
gh run list --branch codex-auto-dev --limit 5
```

若有 ≥ 2 个 `in_progress` run, 等到只剩 0-1 个再 push. 高负载时段大 commit 跟 worker 撞上会让 worker 一窝蜂 rebase 失败 —— 等一个安静窗口再发.

## worker 冲突由 worker 端 codex 兜底处理

worker 现在 (≥ 2026-05-03) 已经有 `693fb128` / `001d0c3d` / `0cdf518c` 三个 fix: rebase 冲突 abort + stash pop, 留脏调 codex 兜底, PID-lock 防双 orchestrator. 大 commit 撞 worker 不再是灾难, 顶多 worker 当轮重试. 你这边责任只是 *atomic commit + merge sync + 选安静窗口*.

## 历史教训

2026-05-03 RH 路线图 commit (`da6e6e10`, 16 文件 / 2108 行) 撞上并行 worker 触发 rebase 风暴, 三个 fix commit 上线后才稳. 当时一度想用"HOT 文件单独 commit + 等 30 秒 + 内容文件 commit"两步法防御, 但那做法会让 commit A 处于编译失败状态 (引用了未 push 的章节文件), 反而更糟. 正确教训是: 单 commit 原子, merge 不 rebase, 选安静窗口.

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

- 构建过程必须可复现 (上述完整本地验证命令)
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
