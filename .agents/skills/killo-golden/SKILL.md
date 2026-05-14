---
name: killo-golden
description: 根据论文目录下的跟踪文档, 选取 papers/bedc/parts/visions 中最容易实现的未实现任务, 进行科研论文编写工作
disable-model-invocation: true
---

## Goal

修改 `papers/bedc/parts/visions`.

## Scope

- 工作范围以 `papers/bedc/parts/visions` 为主.
- 先阅读论文目录下与 visions 相关的索引、跟踪文档、引用关系和相邻章节, 再选择最容易与现有文本融合的未实现任务.
- 如任务需要同步实验, 创建实验脚本并接入对应 `run_all.py` 管线; 仅运行该实验脚本, 不运行整条 `run_all.py`.
- 不自动编译 PDF.

## 注意事项

- 学术化语言.
- 严格禁止口语口吻, 例如不要使用“新xxx”“补充的八条协议侧离散对象结论”“补充 A”“结论 1”等表述.
- 禁止各种人工前缀, 如“结论 A:”“闭环 1:”等.
- 禁止出现显示时间类描述、注释, 禁止记录什么时候修改及相关描述性语言.
- 完全理解后再修改.
- 聊天回复保持简短.
- 修改必须完美融合进入文章, 不要有拼接痕迹.
- 不要手工编号; 如需要编号, 使用 LaTeX 自动编号.
- 单个文件超过 600 行即不向该文件添加内容, 新建同主题 sibling 文件并通过合适的 hub 或索引接入.
- 遵守项目 `AGENTS.md` / `CLAUDE.md` 的 LaTeX 数学环境、hub-only 索引文件、Lean marker、closurestatus 与写作纪律.

## Workflow

1. 阅读 `papers/bedc/parts/visions/index.tex`, `papers/bedc/parts/visions/_index_files.tex`, 相关 tracking 文档, 以及目标章节附近的引用上下文.
2. 用 `wc -l` 检查候选 `.tex` 文件行数; 超过 600 行时不直接追加正文.
3. 选取最小、最容易落地、能自然融入 visions 现有论证链的任务.
4. 在原章节内就地整合; 若需要新文件, 使用内容 slug 命名, 并通过对应索引文件接入.
5. 检查新增文字是否存在口语化前缀、迭代叙事、手工编号、时间性描述和禁用数学环境.
6. 如新增 Lean marker, 确认目标真实存在并遵守 primary/variant 规则.

## User Input

```text
$ARGUMENTS
```

你一定理解用户输入后, 再修改论文, 使其学术化地融入原文. 无需询问用户, 直接修改论文.
