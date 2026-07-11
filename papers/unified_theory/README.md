# unified_theory — 大一统理论的 mathlib 形式化 (隔离子项目)

本子项目形式化"大一统理论": 一个把各种理论/论文连接起来的框架 —— 其自动化科研模式
是搜本论文产出跟其他论文之间重合/对应的公式。目标是**先把该理论的逻辑用 Lean 形式化,
验证逻辑自洽**, 再谈其上层自动化对应搜索。

正式理论内容由用户提供; 当前仓库内只放隔离骨架, 内容落地后在此展开。

## 隔离约定 (两重隔离)

1. **进程隔离**: 本工作线跑在独立 git worktree `newmath-unified` / 分支 `feat/unified-theory-mathlib`,
   与主树 `feat/bio-reality-deepening`(bio_reality 自驱 daemon 所在)物理分离, 互不干扰 git HEAD。

2. **形式化隔离 (mathlib vs mathlib-free)**: 本项目 `lean4/` 是**独立 lake 项目**, 自带
   `lean-toolchain`、自带 manifest、`require mathlib`。它与主仓库 mathlib-free、0-axiom 的
   `lean4/BEDC/` 核心完全隔离:
   - `lean4/BEDC/**` 永不 import 本项目;
   - 本项目不写回、不污染 BEDC 的 mathlib-free / 0-axiom invariant;
   - 用 mathlib 只是因为对应/等价/保结构的形式化在 mathlib 上简单得多, 本体系此处无 mathlib-free 约束。

   同一隔离模式的既有先例: `papers/bedc_mathlib_bridge/lean4`(BEDC↔mathlib 校准桥)。

## 构建

```bash
cd papers/unified_theory/lean4
lake exe cache get      # 下载 mathlib 预编译 olean
lake build              # 编译本项目 (默认 target UnifiedTheory)
```

toolchain 与 mathlib 均 pin 在 `v4.28.0`(与主仓库 lean toolchain 同版, 便于共享 mathlib cache)。

## 命名

`unified_theory` / `UnifiedTheory` 为占位名。正式理论主题确定后按内容重命名 (无版本号)。
