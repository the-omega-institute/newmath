import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tail calculus

第十二章 tail 演算的 Lean 核心: 无穷读数由共尾有限窗口、tail 预算
与分层闭合管理组织。本文件形式化 12.6 原则中可证的一部分: tail
证书可加, 且受趋零预算控制的 residual 被围合到零。因此数值验证可
表达为有限读数加受控尾。
-/

open Filter Topology

namespace UnifiedTheory.Kernel

/-- residual `r` 被 tail 预算 `b` 逐点控制。 -/
def TailControlled (r b : ℕ → ℝ) : Prop :=
  ∀ n, |r n| ≤ b n

/-- 定理 12.4: tail 证书对 residual 加法封闭。 -/
theorem tailControlled_add {r₁ r₂ b₁ b₂ : ℕ → ℝ}
    (h₁ : TailControlled r₁ b₁) (h₂ : TailControlled r₂ b₂) :
    TailControlled (fun n => r₁ n + r₂ n) (fun n => b₁ n + b₂ n) := by
  intro n
  calc
    |r₁ n + r₂ n| ≤ |r₁ n| + |r₂ n| := abs_add_le _ _
    _ ≤ b₁ n + b₂ n := add_le_add (h₁ n) (h₂ n)

/-- 两个趋零 tail 预算的和仍趋零。 -/
theorem tailBudget_add_tendsto_zero {b₁ b₂ : ℕ → ℝ}
    (h₁ : Tendsto b₁ atTop (𝓝 0)) (h₂ : Tendsto b₂ atTop (𝓝 0)) :
    Tendsto (fun n => b₁ n + b₂ n) atTop (𝓝 0) := by
  have h := h₁.add h₂
  simpa using h

/-- 推论 12.5: 受趋零 tail 预算围合的 residual 本身趋零。 -/
theorem tendsto_zero_of_tailControlled {r b : ℕ → ℝ}
    (hc : TailControlled r b) (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto r atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero r]
  exact squeeze_zero (fun n => abs_nonneg (r n)) hc hb

end UnifiedTheory.Kernel
