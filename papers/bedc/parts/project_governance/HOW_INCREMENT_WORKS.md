# HOW_INCREMENT_WORKS

## 目标

本文件规定 BEDC 理论扩展时的编辑方式。规则是按主题修订当前文本：新增内容进入对应章节，活跃表述发生变化时同步更新正文与状态表，机器审计强制 paper-Lean 对齐。

## 1. 放置新章节或新小节

- 如果新内容属于已有主题，把新的 `\chapter` 文件放到 `parts/<theme>/` 下。
- 已有主题的 wrapper 文件保持版本无关命名，例如 `parts/proof_obligations.tex`、`parts/concrete_hardening.tex`。
- 如果新内容引入全新主题，新建 `parts/<new_theme>/` 目录，并新增 `parts/<new_theme>.tex` wrapper。
- `main.tex` 只输入主题 wrapper，不直接输入按时间顺序堆叠的主题文件。

## 2. label 命名

- 章节级 `\label{ch:<theme>-<concept>}`，section 级 `\label{sec:<theme>-<concept>}`。
- 定理级 `\label{thm:<concept>}`、定义级 `\label{def:<concept>}`、命题级 `\label{prop:<concept>}` 等。
- 禁止包含 `vNNN-`、`v1.5.X` 等版本前缀。

## 3. 增加 Lean 目标

- 在 `lean4/BEDC/` 下为新对象选择对应模块；若现有模块不合适，再新增模块。
- 不允许添加 `axiom`：原始对象用 `inductive` / `def` / `class` / `structure` 字段编码（决策树见 `CLAUDE.md` 与 `AGENTS.md`）。
- 写 `theorem T : ... := <real proof>`，禁止 `sorry`；如果暂时无法证明，改写定理形式或选其他目标。

## 4. 论文中标注 Lean 状态

- 在论文章节调用对应的 `\leanchecked{Lean.target.name}` / `\leanstmt{...}` / `\leandef{...}` 宏（下划线写成 `\_`）。
- 每个 Lean 目标在论文中**只标注一次**（primary site）。`lean_scaffold_contract.tex §41.4` 是例外。
- 状态变化时（sorry → checked、def → checked）同一 commit 更新 marker。

## 5. 更新治理状态

- `papers/bedc/frontmatter/status.tex` 记录当前活跃状态，不是历史快照仓库。
- 新定理或新接口如果改变活跃 contract，需要在 `status.tex` 中新增或更新对应行。

## 6. 记录理论修订规则

- 每个会改变活跃读取方式的扩展，都要在“Theory Amendment Policy”章节补充当前规则。
- 记录内容至少说明三点：
  - 当前对象所在位置
  - 当前活跃表述是什么
  - 哪些旧名字或旧说法不再作为引用入口
- 如果只是补证明、不改活跃解释，可不增加新条目；但若改变读者应引用的章节、关系或 theorem，必须登记。

## 7. 验证顺序

- 先改论文。
- 再加 Lean target。
- 再改 `status.tex` / “Theory Amendment Policy”章节。
- 最后运行四项审计：
  - `cd lean4 && lake build`
  - `cd papers/bedc && make`
  - `python3 tools/check-axioms.py`
  - `python3 lean4/scripts/bedc_ci.py audit`（强制 `\leanchecked{X}` 的 X 在 Lean 真存在）

## 8. 禁止事项

- 不恢复按版本后缀命名的 `parts/..._v1_5_x/` 目录。
- 不把治理说明写进章节正文里替代治理章节记录。
- 不添加 `axiom` 与 `sorry`。
- 不写未在 Lean 真存在的 `\leanchecked{X}` 宏（audit 会拒绝）。
