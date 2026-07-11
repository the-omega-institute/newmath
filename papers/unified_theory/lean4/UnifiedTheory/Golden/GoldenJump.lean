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

/-- 黄金跳跃是二值 Beatty/Sturmian 词:`S` 每步增加 `1` 或 `2`。 -/
theorem goldJump_mem (n : ℕ) : goldJump n = 0 ∨ goldJump n = 1 := by
  let τ : ℝ := Real.goldenRatio - 1
  let z : ℝ := ((n : ℝ) + 1) * τ
  have hτpos : 0 < τ := by
    dsimp [τ]
    linarith [Real.one_lt_goldenRatio]
  have hτlt : τ < 1 := by
    dsimp [τ]
    linarith [Real.goldenRatio_lt_two]
  have hbase : ((n : ℝ) + 1) * (Real.goldenRatio - 1) = z := by
    dsimp [z, τ]
  have hnext : ((n : ℝ) + 2) * (Real.goldenRatio - 1) = z + τ := by
    dsimp [z, τ]
    ring
  have hlow : (⌊z⌋ : ℤ) ≤ ⌊z + τ⌋ := by
    exact Int.floor_le_floor (by linarith)
  have hfloor_one : (⌊z + (1 : ℝ)⌋ : ℤ) = ⌊z⌋ + 1 := Int.floor_add_one z
  have hhigh0 : (⌊z + τ⌋ : ℤ) ≤ ⌊z + (1 : ℝ)⌋ := by
    exact Int.floor_le_floor (by linarith)
  have hhigh : (⌊z + τ⌋ : ℤ) ≤ ⌊z⌋ + 1 := by
    simpa [hfloor_one] using hhigh0
  rw [goldJump_eq_floor_diff n, hnext, hbase]
  omega

end UnifiedTheory
