import Mathlib.Tactic

/-!
# 隔离自检 (isolation sanity)

本文件只证明: mathlib import 能在隔离的 `unified_theory` lean 项目内正常解析,
且独立于 mathlib-free 的 `lean4/BEDC/` 核心。

真正的大一统理论形式化内容待用户提供后落地; 落地时替换/扩展本占位模块。
-/

namespace UnifiedTheory

/-- mathlib tactic (`norm_num`) 在本项目可用, 隔离链路打通。 -/
theorem isolation_sanity : (1 : ℕ) + 1 = 2 := by norm_num

end UnifiedTheory
