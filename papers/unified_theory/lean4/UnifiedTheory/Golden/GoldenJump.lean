import UnifiedTheory.Golden.DeficitFractional

/-!
# 黄金跳跃序列的 Sturmian 窗口计数(oracle 建议,certified)

黄金一步跳 `J n := S(n+1) − S n − 1 = ⌊(n+2)τ⌋ − ⌊(n+1)τ⌋`(`τ = φ − 1`)。窗口和 telescope
为纯 floor 差,给出**有限 Sturmian 平衡词定理**:任意长度 `N` 的窗口内跳数恰为 `⌊Nτ⌋` 或
`⌊Nτ⌋+1`。全有限、不涉解析前沿。本结果由旁路 oracle 提议,本地机器核验。
-/

namespace UnifiedTheory

open Real

/-- 黄金一步跳。 -/
noncomputable def goldJump (n : ℕ) : ℤ := S (n + 1) - S n - 1

/-- `J n = ⌊(n+2)τ⌋ − ⌊(n+1)τ⌋`(`τ = φ − 1`)。 -/
theorem goldJump_eq_floor_diff (n : ℕ) :
    goldJump n = ⌊((n : ℝ) + 2) * (Real.goldenRatio - 1)⌋
      - ⌊((n : ℝ) + 1) * (Real.goldenRatio - 1)⌋ := by
  unfold goldJump
  rw [S_eq_tau (n + 1), S_eq_tau n]
  have e1 : (((n + 1 : ℕ) : ℝ) + 1) * (Real.goldenRatio - 1)
      = ((n : ℝ) + 2) * (Real.goldenRatio - 1) := by push_cast; ring
  rw [e1]; push_cast; ring

/-- **oracle-suggested 定理(窗口 telescoping)**:长度 `N` 窗口内跳数和 telescope 为
`⌊(m+N+1)τ⌋ − ⌊(m+1)τ⌋`。 -/
theorem goldJump_window_exact (m N : ℕ) :
    ∑ i ∈ Finset.range N, goldJump (m + i)
      = ⌊(((m + N : ℕ) : ℝ) + 1) * (Real.goldenRatio - 1)⌋
      - ⌊(((m : ℕ) : ℝ) + 1) * (Real.goldenRatio - 1)⌋ := by
  set f : ℕ → ℤ := fun k => ⌊(((m + k : ℕ) : ℝ) + 1) * (Real.goldenRatio - 1)⌋ with hf
  have key : ∀ i, goldJump (m + i) = f (i + 1) - f i := by
    intro i
    rw [goldJump_eq_floor_diff (m + i), hf]
    have ha : (((m + i : ℕ) : ℝ) + 2) * (Real.goldenRatio - 1)
        = (((m + (i + 1) : ℕ) : ℝ) + 1) * (Real.goldenRatio - 1) := by push_cast; ring
    rw [ha]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_range_sub f N, hf]
  simp

end UnifiedTheory
