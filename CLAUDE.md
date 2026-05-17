# 工作规范

> 本文件是项目所有 AI agent (Claude Code / Codex / Cursor / Cline / Aider) 的**唯一规范源**. 仓库根 `AGENTS.md` 是本文件的 symlink, 不是独立文档. 跨工具指引看本文件即可.

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
- **禁止版本号 / round 编号在任何命名工件**: 文件名 / 命名空间 / 定理名 / 论文段落标题 / branch 名 / worktree 路径 / commit subject / PR title / codex worker 任务名 都不带 `V2` / `V6` / `V7` / `R11` / `Rxx` / `Round N` / `rN-X` / `v[0-9]+` 这类迭代标签. 命名按内容主题 (例: `feat-conf-closed-strip-completion` 而非 `feat-conf-general-v2`; `Typing.lean` 而非 `TypingV2.lean`; "Shift-aware binder context" 而非 "V7 substrate"). 派 codex worker 前自检 branch / worktree / file path 含 `v[0-9]+` / `V[0-9]+` / `r[0-9]+` / `Round` 字样 → 重命名
- 不生成修改记录、日志、总结、变更原因、报告
- 不添加文件内备注
- 有问题直接改, 无需备份

## 数学符号写法

- 行内数学: `$...$`
- 展示数学: `$$...$$` (每个 `$$` 占独立一行)
- 多行展示: 在 `$$...$$` 内部使用 `\begin{aligned}...\end{aligned}` 或 `\begin{gathered}...\end{gathered}`
- **禁止顶层使用**: `\[...\]`, `\begin{equation}`, `\begin{equation*}`, `\begin{align}`, `\begin{align*}`, `\begin{eqnarray}`, `\begin{eqnarray*}`
- `papers/bedc/Makefile` 的 precheck 调 `scripts/check_math_env.sh`, 在 build 前**自动**把违规重写为 `$$\begin{aligned}...\end{aligned}$$` 形式; 写入禁用模式不会编译失败, 但会被静默替换
- 编写时直接用 `$$` 形式; 不要依赖 auto-rewrite 兜底

## LaTeX 常见 fail 模式

- **Math 宏在 text-mode 位置**: `\<Capital>Up` 类宏 (`\NatUp`, `\BoolUp`, ...) 是 `\mathsf{...}^{\uparrow}` 的封装, **必须在 math mode 内**. 典型错误包括 `\falsifiablePrediction{... \ClosedGenerationRefusalUp.}` 这类文本命令参数内裸用, 以及 `dyadicratcore/l10_sibling_dependency_route.tex:1: \DyadicRatCoreUp reads...` 这类文件首行直接 text mode. 修法: 包成 `$...$`. precheck check L 会拦.
- **死 `\input` 路径**: worker 把 region 内容迁到 subdir 后, sibling 文件若残留指向已搬走文件的 `\input{...}`, CI 会报 "File not found". 修法: 修路径或删行. precheck check M 会拦.
- **`\falsifiablePrediction{}` / `\independenceWitness{}` 参数语义**: 这两个宏是 text-mode 段落输出 (`\par\textbf{...}: #1\par`). 参数里任何 math 内容必须 `$...$` 包裹. 数学公式建议改用 `$$...$$` 展示式, 不要塞进参数.

## 项目结构

- `lean4/` — Lean 4 形式化, mathlib-free, 0 axiom 0 sorry
- `papers/bedc/` — BEDC LaTeX 论文 (现行态)
- 多文件 concrete-instances region 采用 hub + subdir 布局:
  - 顶层 hub 文件: `papers/bedc/parts/concrete_instances/<NN>_<slug>_namecert_construction.tex`. 只放 `\input{parts/concrete_instances/<slug>/<name>.tex}` 行; 可放 1-2 句 orienting 段和 `\closureat{<X>Up}{<level>Str}` 状态行; **禁** `\chapter` / `\begin{theorem}` / `\begin{definition}` / `\begin{lemma}` / `\begin{proof}` / `\begin{closurestatus}` / 任何正文环境.
  - Subdir spine: `papers/bedc/parts/concrete_instances/<slug>/namecert_construction.tex`. 持有 `\chapter{...}` / `\label{ch:concrete-instances-<slug>-namecert}` / `\origin{...}` / 章节 intro + 第一批定义.
  - 其它 sibling: `papers/bedc/parts/concrete_instances/<slug>/<descriptive_name>.tex`. 文件名 lowercase snake_case, 不带 `<NN>_<slug>_` 前缀.
  - Hub 内 `\input` 顺序: spine 第一, 其余按主题逻辑 (constructor → theorem → bridge → closurestatus).
- `papers/bedc/parts/project_governance/theory_amendment_policy.tex` — 持续发展规则
- `papers/bedc/parts/project_governance/HOW_INCREMENT_WORKS.md` — 增量配方
- `lean4/scripts/bedc_ci.py` — paper-Lean drift 审计 (`\leanchecked{X}` X 必须真存在); 子命令以 `python3 lean4/scripts/bedc_ci.py --help` 为准, 本文档不复述
- `tools/check-axioms.py` — axiom 禁用审计脚本 (CI gate)

## 信息治理: 单一真实源 + 指针思维

仓库内**同一事实只允许一处定义**, 其他地方只通过指针引用. 复述会产生漂移, 任何"两份同义说明"必须被消去一份.

**唯一真实源 (single source of truth) 划分**:

- **规范 / 不变量 / 命名约定 / 工作流程** → 唯一源是本 `CLAUDE.md`. 任何其他文档若描述规范, 引这里, 不复述
- **形式化事实** (定理状态、章节存在性、闭合等级、命名空间命中点、saturation 数字) → 唯一源是 `lean4/BEDC/` + `papers/bedc/parts/` 的实际内容, 通过 `bedc_ci.py` / `critical_path.py` / `grep` 实时读出, 任何文档不缓存这些数字
- **工具能力** (脚本子命令、参数、输出格式) → 唯一源是脚本自身的 `--help` 与 `--json` 输出, 本文档不列子命令清单

**Skill / memory / 文件内注释纪律**:

- 只承载**方法** (怎么查、用什么命令组合、怎么解读输出) 与**指针** (去 `bedc_ci.py audit` 看 X, 去 `critical_path.py` 看 Y)
- **不复述**: 当前热点命名空间 ("leanstmt 集中在 BEDC.Reflection.\*")、具体阈值 ("某文件 7d 改 ≥ 100 次")、saturation 数字、章节存在性断言
- 写 skill / memory 时, 凡是"会过时的事实", 应该改成"读源命令 + 让模型自己判断"

**冲突处理**:

- skill / memory / 注释跟 `CLAUDE.md` 冲突 → 信 CLAUDE.md, 报告并消除 skill / memory 漂移
- `CLAUDE.md` 跟代码 / 实际工具输出冲突 → 信代码, 立即修正 CLAUDE.md
- 任何分析任务首要任务之一是检测漂移; 发现就在报告里列出, 不要默默遵循过时规范

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
- **禁止 statement-only 避 sorry 模式**: 不得在 lean4/ 写 `def Foo_Statement : Prop := ∀ ...` + `theorem Foo_well_formed : True := True.intro` 这类组合让 paper 端 `\leanchecked` 指向它, 同时用 `True.intro` stub 假装"被 Lean 接受". 这是隐藏 sorry 的等价物 — 把未证 hypothesis 包装成 named def, 但实质内容没被 kernel verify. 如果当前无法证某条 hypothesis, 选项: (a) 不在 lean4/ 登记该目标, 仅在 paper 端用 `\leanstmt` 描述 statement-only target; (b) 改写定理形式让 unconditional 证明可行; (c) 把它登记为 `class`/`structure` 字段 (Setup typeclass 路径, 让 carrier 实现去 discharge). 任何 `_Statement` 后缀 def + `_well_formed : True := True.intro` 这类 idiom 一律拒绝

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

闭合等级 (理论轴) 取自 `seedClosure | obligationClosure | scopedClosure | publicClosure | bridgedClosure | matureClosure`, 验证等级取自 `unformalized | formalTarget | encodedDef | scaffoldChecked | theoremChecked | auditClean | axiomClean | bridgeChecked`. 这两组等级名以 `papers/bedc/preamble.tex` 实际宏定义为准, 实际分布以 `grep "\\theoryclosure{" papers/bedc/parts/` 与 `grep "\\formalstatus{" papers/bedc/parts/` 为准.

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
cd lean4 && lake build                                  # 0 axiom, 0 sorry, build OK
cd papers/bedc && make                                  # pdflatex 双趟, 生成 PDF (~75s)
python3 tools/check-axioms.py                           # 源代码 axiom 禁用审计
python3 lean4/scripts/bedc_ci.py audit                  # paper ↔ Lean drift 审计
python3 lean4/scripts/bedc_ci.py axiom-purity           # 传递依赖审计 (禁 Classical.choice / Quot.sound)
```

上述命令全部 exit 0 才算 ship 标准.

## `\origin{}` 标签语义

每章顶部的 `\origin{}` 标记**理论 lineage**, 不是作者身份:

- `\origin{human}` — 人类数学传统已有的概念 (例: Cauchy completion, metric space, manifold chart, abelian category) 在 BEDC 体系内的 NameCert reconstruction. 这些章节多数仍由 codex worker 写出, 因为 codex 在把已知数学翻成 BEDC 的 carrier / NameCert 形式; 这是正常工作, 不是 lineage 篡改. 章节 intro 通常以 "Following Bishop and Bridges / Bourbaki / ..." 形式引经典文献作 ground
- `\origin{ai}` — BEDC 体系内自身 discovery 的新 primitive 概念 (例: DigestLoopRefusal, ApophaticFarEndSocket, TasteGate, AuthorizedGeneratorRecursor), 人类数学传统中无直接先例. 章节 intro 通常以 "The X packet realizes the Y branch of \autoref{vision/sec/...} as finite NameCert data" 形式 ground 在某个 visions / philosophy 段定义
- `\origin{ai-composite}` — BEDC 体系内 derivative packet, 把 3+ 个已有 ai 章节 bundle 成一个新组合 surface. 不是独立 discovery, 是 surface bundling / integration. 章节 intro 通常以 "composite over [3+ siblings]" 或 "joins / composes [several existing chapters]" 形式声明依赖. 用于 conservativity-audit 区分 "load-bearing 新发现" 与 "AI 衍生组合"
- 三者 lineage 区分是 `bedc_ci.py conservativity-audit` 的基础, 用于追踪 baseline ↔ discovery 引用图; `ai-composite` 节点视同 ai 但不算 import 进 baseline 的独立新概念

`bedc_ci.py conservativity-audit` 是**可选的信息性 survey**, 不是 ship gate: 它列出 baseline (`\origin{human}`) 章节里 import 了 ai (`\origin{ai}`) 章节模块的 edge, 始终 exit 0. 想看 baseline ↔ ai 引用图时单独跑. 项目立场: 只要 taste 够, baseline 引用 ai-discovered 结构是允许的, 这是 theory discovery 的正常形态.

## 开发循环: 用 `make check` 代替 `make`

提交 / 出版前用 `make` (双趟, 生成 PDF, 解析 `\autoref` / TOC). 平时反复改章节、试错时用 `make check` —— 单趟 `pdflatex -draftmode`, 大约一半时间 (40s vs 75s), 仍然抓到所有真错误 (Undefined control sequence / Missing $ / Extra } / unresolved `\input` / package errors). 唯一代价: 交叉引用印成 `?? on page ??`, 对开发循环不影响. **不要在 ship 前用 `make check` 替代 `make`**: 你需要看 PDF 真实出来, 也需要确认所有 `\autoref` 解析 (CI 会查).

`axiom-purity --strict` 用 `#print axioms` 检测每条 BEDC 定理的传递依赖, 强制零 Lean stdlib 公理依赖: 禁 `Classical.choice` (LEM/选择公理)、`Quot.sound` (商类型公理) 和 `propext` (命题外延). BEDC 全部定理纯 CIC 派生, 不依赖任何 stdlib 公理, 跟 Brouwer / Bishop 严格 constructive 同档.

## CI

`.github/workflows/lake-build.yml` 在 `lean4/**` 或 `tools/check-axioms.py` 改动时触发:

1. `cd lean4 && lake build`
2. `python3 tools/check-axioms.py`

任一失败 PR 不可合并.

---

# Codex pipeline 协作纪律

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

# Claude Code 一次性 codex CLI 并行调用

上节是 `codex_formalize.py` 常驻 worker. **本节**: Claude Code 在一个 session 里把任务 fan-out 给多个独立 codex CLI session, 各自跑在 worktree 隔离里, 完后 orchestrator 串起来 merge + PR. 跟常驻 worker 是两套机制, 不共享 PID lock.

## 命令模板 (codex 0.130+)

```bash
codex exec --dangerously-bypass-approvals-and-sandbox -C <worktree-path> "$(cat /tmp/prompt-X.md)"
```

- `exec` = non-interactive, 不带就进 TUI
- `--dangerously-bypass-approvals-and-sandbox` 跳所有 approval + sandbox (用户授权 "所有权限" 时用); 否则每个文件写卡确认
- `-C <dir>` 让 codex 自己 chdir, **不要** `cd <wt> && codex`
- 长 prompt 写到 `/tmp/prompt-X.md` 再 `$(cat ...)` 读, inline 长 arg 易 shell escape 出错

## Fan-out 流程

```
git worktree add -b worker-X /tmp/wt-X <base>     # 每单元一个 worktree, branch 名前缀统一
# 三个 codex exec 同 message 用 Bash run_in_background: true, 输出 redirect 到 /tmp/codex-worker-X.log
# task-notification 到达 → tail log + git -C <wt> log --oneline 验证 commit
git checkout -b feat/<name> origin/<target>       # 从最新 origin 起 (不是 local 旧 HEAD)
git merge --no-ff worker-X                        # 逐个; 文件集若提前划清就无冲突
# 完整本地验证: lake build + check-axioms + bedc_ci.py audit + axiom-purity --strict
git push -u origin feat/<name>
gh pr create --base <target> ...
gh pr checks <PR> --watch                         # Bash run_in_background: true 守 CI 终态
gh pr merge <PR> --merge --delete-branch          # 用户授权 merge 后
git fetch origin <target> && git pull --ff-only origin <target>  # 立即同步, 否则本地 <target> 落后远端
git worktree remove /tmp/wt-X; git branch -d worker-X  # 已 merge, lowercase -d 即可
```

## codex prompt 必含项 (省 retry)

codex session 没对话上下文, prompt 必须自洽包含:

- 项目 invariants 摘要 (mathlib-free / 0 axiom / 0 sorry / 工作语言中文)
- **文件白名单** + **DO NOT 列表** (worker 不能跨界, 否则 merge 冲突)
- 共享接口规约 (跨 worker 一致的类型签名 / 数据结构必须 freeze 在 prompt 里)
- 验证准则 (例 `cd lean4 && lake build` 必 exit 0)
- commit 消息模板 (含 R 编号)
- 显式 "不要 push remote, orchestrator 来 merge"

## 计时与 /loop 配速

- 单 codex worker 5-15 min 典型 (50-300 行 Lean / Python)
- Bash `timeout: 600000` (10 min) 兜底
- /loop dynamic mode fallback wakeup 1500-1800s; task-notification 通常早于 fallback

## Bash 跨 call 陷阱

`cd` 跨 Bash call **持久**. `cd lean4 && lake build` 之后下一个 Bash 还在 `lean4/`, 相对路径 `lean4/scripts/X.py` 解析成 `lean4/lean4/scripts/X.py` 出错. 复位: 绝对路径 (`/Users/auric/newmath/...`) 或 `cd /Users/auric/newmath && ...`.

## 安静窗口

push feat 分支不直接撞 codex-auto-dev worker (不同 branch), 但 `gh run list --branch codex-auto-dev --limit 5` 仍是 sanity check, 避免 CI runner 池拥塞.

## CI 监控异步化, 不阻塞开发

PR push 后**不要同步等 CI**: PDF job 通常 4-6 min, Lean4 job 1-2 min, 同步 `gh pr checks --watch` 把这段时间烧在阻塞等待上. 改用一个 Monitor 拉远端 status:

```bash
# Bash run_in_background: true
gh pr checks <PR> --watch --interval 30 > /tmp/pr<PR>-ci.log 2>&1
```

`run_in_background: true` 让任务挂着, 完成时发 task-notification 唤回. 同时继续派遣下一轮 codex worker / 写代码 / 跑本地 build —— 不浪费 wall clock.

**等待开发循环**: codex worker 也 background dispatch, 同样靠 task-notification 唤回. 一个典型回合: dispatch 3 worker (background) + 在 PR 上 push 新内容 + 对每个 worker arm 一个 Monitor (background) 等其 commit + `ScheduleWakeup` 长 fallback (1h+). 然后这个 turn 结束, harness 在事件触发或 fallback 时唤回.

**绝不**用 `gh pr checks <PR> --watch` 在前台同步等. 也**绝不**在 worker 都 background 后立刻 `wait` (除非真的没下一步可做). **也不要靠 ScheduleWakeup 固定 25 min 节奏**: codex worker 完成时间方差大 (3-15 min), 固定 wakeup 浪费 cache window + 不及时. 改用 Monitor 等真信号.

**Worker 完成回调**: 最简单做法是直接用 Bash `run_in_background: true` 跑 `codex exec ...` (**不要**在尾部加 `&`). codex 本身阻塞执行 5-15 min, 退出时 harness 发 task-notification. 一个 worker 一个 Bash 调用, 3 个 worker 就并行 3 个 background Bash, 各自完成各自发回调.

```bash
# Bash 调用, run_in_background: true, 不要内部 & 后台化
codex exec --dangerously-bypass-approvals-and-sandbox -C /tmp/wt-X "$(cat /tmp/prompt-X.md)" > /tmp/codex-log-X.log 2>&1
```

错误做法: `codex exec ... &` 在 Bash 里, bash 立即 fork+退出, 永远收不到 codex 完成事件. 也不要靠 ScheduleWakeup 固定 25 min 节奏 polling, 既不及时又烧 cache.

Monitor 工具留给"事件流"型监视 (CI 多个 check 状态变化, 日志新错误行). 单次"等命令完成"用 Bash background 就够.

CI 失败诊断也尽量懒处理: 如果 PDF 失败是上游 codex 引入的未定义宏 (历史复现: `\origin` / `\ChapterTasteGate` / `\GroundCompiler` / `\BHist`), 加 preamble stub macro 即可, 不阻塞.

**上游 codex sibling 重复**: 上游 codex 偶尔把 monolithic 文件拆成 sibling (Confluence.lean → Confluence/Core.lean + AtomShape.lean + ...). 我合并时若也加了相同内容到 monolithic, lean 编译会报 "已 declared" 重复. 解决: 删 monolithic 留 sibling (或反向), 让导入清单只指一边.

---

# Codex worker 失败模式 (并行 fan-out 经验)

orchestrator 把任务 fan-out 给 codex CLI worker, 一轮 5-8 个常见. 失败模式按概率排序:

## 1. API 容量满中途 exit (exit code 1)

worker 跑到一半碰到 `ERROR: Selected model is at capacity. Please try a different model.` 直接退出. worker tree 留下半成品文件 (新增 + 修改), 但**没有任何 commit**. `git status` 显示 dirty, `git log` 显示分支只指向 base.

处理: **abandon 整单**. 不要手工捡 worker 写到一半的代码再 commit —— 它没编译过, 通常 elaboration 错或 propext leak. 等 API 恢复重派.

## 2. exit code 0 不等于 build OK

worker 完成回调 (exit 0) 只说明 codex 自己 prompt loop 走完, **不是** lake build 通过. orchestrator 在 merge 前必须独立验证:

```bash
cd /tmp/wt-X/lean4 && lake build
```

(注意必须在 `lean4/` 子目录, 不是 worktree 根 — lakefile.lean 在 `lean4/lakefile.lean`. 根目录跑会报 `no configuration file with a supported extension`.)

跑出 `error: build failed` 直接 abandon, 不 merge.

## 3. propext / Classical.choice / Quot.sound 泄漏

即便 prompt 显式警告 "nested pattern match 会触发 propext", worker 经常仍然写出泄漏代码. axiom-purity --strict 抓住:

```
[bedc-ci] axiom-purity: theorems=N pure=N-1 impure=1 forbidden=['Classical.choice', 'Quot.sound', 'propext']
[bedc-ci] axiom-purity FAIL: 1 forbidden dependency(s)
```

处理: **abandon, 不要手工 "修一下"**. propext leak 通常需要重构 `def` 形态 (拆嵌套 match, 引入辅助 helper), 不是局部 tactic 调整能修的. 重派或自己重写.

## 4. worker branch 名 ≠ worktree 路径

派单时一般 `git worktree add -b feat-X /tmp/wt-X <base>`. merge 时**用 branch 名**, 不是路径:

```bash
git merge --no-ff feat-X        # 对
git merge --no-ff /tmp/wt-X     # 错: "not something we can merge"
```

worker 内部可能改了 branch 名 (codex 偶尔自己重命名), merge 前 `cd /tmp/wt-X && git branch --show-current` 拿真名.

## 5. `git diff origin/auto-dev..HEAD` 显示 "deleted" 文件不是真删

多 worker 并行: worker A 的 branch 基于派单瞬间的 auto-dev tip. 派单后 worker B / C 已 merge 进 auto-dev. 这时 `git diff origin/auto-dev..HEAD` 在 worker A 视角下, 别人加的文件显示 "deleted" (因为 A 的 HEAD 没那些文件).

但 `git merge feat-A` 用 three-way merge 拿 merge-base (= 派单时的 auto-dev tip, 不是当前 origin/auto-dev), 自动并入 B/C 已加的文件, **不会误删**. 看 diff 输出别恐慌, 直接 merge.

## 6. orchestrator merge 后 push reject

派单完成期间 origin/auto-dev 已被别的 worker (常驻 codex_formalize.py) push 新 commit. orchestrator push 被拒. 用 merge 不 rebase (上方 Codex pipeline 段已说明), 不要 `--rebase`.

## 7. worker prompt 必须显式指定 build step

只写 "build + commit" 太模糊. codex 经常省略 build 直接 commit 半成品. 写:

```
完成步骤:
1. 写文件
2. cd lean4 && lake build (必须 exit 0)
3. cd .. && python3 lean4/scripts/bedc_ci.py axiom-purity --strict (必须 pass)
4. git add ... && git commit -m "..."
5. 不 push, orchestrator 来 merge
```

显式 step 4 后不 push, 否则 worker 偶尔会 push 半成品.

## 8. worker 漏 strip 顶层 hub

worker 把 region 内容迁到 `<slug>/` subdir 时, 容易创建 subdir 副本但忘记把顶层 hub 文件缩到 `\input` 列表. 结果是 hub 与 sibling 两边都有同一 `\leanchecked` 标记, marker uniqueness gate fail.

缓解: worker prompt 必含 `BEFORE commit: cd papers/bedc && make precheck must exit 0`, 并按上方"项目结构"里的 hub + subdir 布局检查 hub 是否只剩结构性内容.

## 9. Sibling 文件残留死 `\input`

worker 迁移文件后, 某 sibling 文件顶部可能还留着指向原顶层路径的 `\input` 行, 例如 `subgroup/quotient_classifier_kernel_rows.tex` 含 `\input{parts/concrete_instances/58_subgroup_namecert_construction_core}`. 静态扫描可能暂时看不出问题, 但 pdflatex 会 fail.

处理: 见 "LaTeX 常见 fail 模式" 的死 `\input` 路径条目. precheck check M 会拦.

## 10. Math 宏裸放 text 上下文

paper 侧自动写作 agent 容易把 `\<Cap>Up` 类宏裸放进 text-mode, 尤其是文本宏参数或文件首行. 这会触发 LaTeX math-mode 错误或输出异常.

处理: 见 "LaTeX 常见 fail 模式" 的 Math 宏在 text-mode 位置条目. precheck check L 会拦.

## 失败单位的清理

abandon 后 orchestrator 处理:

```bash
git worktree remove --force /tmp/wt-X
git branch -D feat-X     # branch 还在但没 merge
```

worker 写的半成品 prompt log 留 `/tmp/codex-log-X.log` 调试用, 别立即 rm.

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
