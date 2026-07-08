import UnifiedTheory.Golden.BeattyDeficit

/-!
# 亏空的 τ-floor 形式(oracle 建议,certified)

由 `φ = 1 + τ`(`τ = φ − 1 = 1/φ ∈ (0,1)`)得 `S n = n + ⌊(n+1)τ⌋`,故亏空的整数部分抵消,
`cDef a b = ⌊(a+1)τ⌋ + ⌊(b+1)τ⌋ − ⌊(a+b+1)τ⌋`——只由 `τ` 的黄金旋转分数部分决定。这把 Beatty
亏空写成纯 `τ`-floor 差,是三值(`cDef∈{−1,0,1}`)之上更精细的旋转-窗口刻画的基础。
本结果由旁路 oracle(ChatGPT Pro)提议,经本地机器核验为真。
-/

namespace UnifiedTheory

open Real

/-- `S n = n + ⌊(n+1)τ⌋`,`τ = φ − 1`(因 `φ = 1 + τ`,整数部分 `n+1` 从 floor 提出)。 -/
theorem S_eq_tau (n : ℕ) :
    S n = (n : ℤ) + ⌊((n : ℝ) + 1) * (Real.goldenRatio - 1)⌋ := by
  unfold S
  have h : ((n : ℝ) + 1) * Real.goldenRatio
      = ((n + 1 : ℕ) : ℝ) + ((n : ℝ) + 1) * (Real.goldenRatio - 1) := by
    push_cast; ring
  rw [h, Int.floor_natCast_add]
  push_cast; ring

/-- **oracle-suggested 定理(亏空 τ-floor 形式)**:整数部分抵消后,
`cDef a b = ⌊(a+1)τ⌋ + ⌊(b+1)τ⌋ − ⌊(a+b+1)τ⌋`(`τ = φ − 1`)。亏空纯由黄金旋转 `τ` 的
floor 差决定,与解析 `φ` 无关。 -/
theorem cDef_eq_floor_tau (a b : ℕ) :
    cDef a b = ⌊((a : ℝ) + 1) * (Real.goldenRatio - 1)⌋
      + ⌊((b : ℝ) + 1) * (Real.goldenRatio - 1)⌋
      - ⌊(((a + b : ℕ) : ℝ) + 1) * (Real.goldenRatio - 1)⌋ := by
  unfold cDef
  rw [S_eq_tau a, S_eq_tau b, S_eq_tau (a + b)]
  push_cast; ring

end UnifiedTheory
