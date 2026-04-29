Cross-tool AI agent guidance (Codex / Cursor / Cline / Aider / Claude Code via CLAUDE.md). For Claude Code-specific skill routing, see CLAUDE.md.

# 工作规范

## 环境与工具链

- Python: 使用 `python3`
- LaTeX: 使用 `xelatex`; `newmath` 采用 `xelatex + xeCJK + listingsutf8`
- 单个 `.tex` 文件不超过 800 行, 超过须拆分
- 二进制运算使用原生实现, 不用二进制字符串
- Lean 4: 使用 `lake build`; `lean4/` 为 mathlib-free 形式化, 从 first principles 起步

## 语言与格式

- 工作语言默认中文, 英文版文档以 `_en.md` / `_en.tex` 结尾
- 数学公式只用 `$` 与 `$$`; `$$` 必须独立成行

## 写作纪律

- 禁止任何修订痕迹: 不出现"新增""修订""修复了上一版本..."等字样
- 不生成修改记录、日志、总结、变更原因、报告
- 不添加文件内备注
- 有问题直接改, 无需备份

## 项目结构

- `lean4/` — Lean 4 形式化, mathlib-free, 从 first principles 起
- `papers/bedc/` — BEDC LaTeX 论文, 以 BEDC v1.5.5 为起步镜像, 采用 append-only 增量发展

---

# The Omega 科研宪章

## I. 第一性原理优先

- 每个结论须能追溯到定义、公理、已证命题或明确假设
- 直觉、命名和物理解释不得替代证明
- Lean 与论文中的主张应保持语义对齐, 不得用叙述掩盖证明缺口

## II. 最小输入原则

- 新增公理、假设、符号或外部机制前, 须先说明最小失败点
- 优先选择依赖更少、结构更短的表述
- 不为叙事完整引入不可检验的额外结构

## III. 显式依赖链

- 每条基础陈述须标明其性质: 定义、公理、假设、猜想、推导结果或经验事实
- 跨层引用须明确依赖方向, 禁止隐含前提
- 论文章节、公式、证明目标与 Lean 命题之间的对应关系必须可审计

## IV. 可证伪与量化约束

- 经验性或数值性主张须附带观测量、误差口径与适用边界
- 纯理论结果须给出至少一种一致性检查: 边界情形、极限行为或已知特例复现
- 负面结果与失败模式必须显式记录, 不得用"未来工作"掩盖

## V. 可复现、可审计

- 构建过程必须可复现: `cd lean4 && lake build`, `cd papers/bedc && make`
- 生成结果须能回溯到源文件与依赖链
- BEDC 增量开发采用 append-only 原则, 审计轨迹必须清晰
