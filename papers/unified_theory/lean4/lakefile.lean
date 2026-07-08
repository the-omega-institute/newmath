import Lake
open Lake DSL

/-
隔离的 mathlib 形式化项目: 大一统 (跨论文/跨理论对应) 理论。

与主仓库 mathlib-free、0-axiom 的 `lean4/BEDC/` 核心完全隔离:
本项目自带 toolchain、自带 lake-manifest、`require` mathlib。
`lean4/BEDC/**` 永不 import 本项目, 本项目也不反向污染 BEDC 的 mathlib-free invariant。
用 mathlib 是为了让对应/等价/保结构的形式化更简单; 本体系此处不受 mathlib-free 约束。

package / lib 名 `unified_theory` / `UnifiedTheory` 为占位, 待正式理论内容落地后按主题重命名。
-/

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

package "unified_theory" where
  leanOptions := #[⟨`maxHeartbeats, 400000⟩]

@[default_target]
lean_lib UnifiedTheory where
