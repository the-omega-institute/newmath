import UnifiedTheory.Golden.GoldenIdentities

namespace UnifiedTheory

open Real

/-!
这是 three-gap / 三距定理(Steinhaus 猜想; Sos/Suranyi/Swierczkowski 1957-59)
黄金案的算术心脏: `α = 1 / φ` 时 Fibonacci 黄金倍数到整数格的距离恰为 `φ` 的负幂。
完整二间隔序结论是经典定理(van Ravenstein 1988), mathlib 无; 此处只机检算术心脏。
-/

/-- 黄金共轭的绝对值是黄金比的倒数。 -/
theorem goldenConj_abs : |goldenConj| = goldenRatio⁻¹ := by
  rw [abs_of_neg Real.goldenConj_neg]
  exact Real.inv_goldenRatio.symm

/--
`F_{n+1} / φ` 到整数 `F_n` 的距离恰为 `φ ^ (-(n+1))`, 写成 Lean 的倒数幂形式。
-/
theorem fib_dist_to_int (n : ℕ) :
    |(Nat.fib (n + 1) : ℝ) / goldenRatio - (Nat.fib n : ℝ)| =
      goldenRatio⁻¹ ^ (n + 1) := by
  have hdiff :
      (Nat.fib (n + 1) : ℝ) / goldenRatio - (Nat.fib n : ℝ) =
        -goldenConj ^ (n + 1) := by
    rw [fib_succ_div_goldenRatio n]
    ring
  rw [hdiff, abs_neg, abs_pow, goldenConj_abs]

/-- 对 `n ≥ 1`, 心脏距离已经小于半个整数格。 -/
theorem goldenRatio_inv_pow_lt_half {n : ℕ} (hn : 1 ≤ n) :
    goldenRatio⁻¹ ^ (n + 1) < (1 : ℝ) / 2 := by
  have hφpos : (0 : ℝ) < goldenRatio := Real.goldenRatio_pos
  have hφne : (goldenRatio : ℝ) ≠ 0 := ne_of_gt hφpos
  have hr0 : (0 : ℝ) ≤ goldenRatio⁻¹ := le_of_lt (inv_pos.mpr hφpos)
  have hrmul : goldenRatio⁻¹ * goldenRatio = 1 := inv_mul_cancel₀ hφne
  have hrlt1 : goldenRatio⁻¹ < 1 := by
    nlinarith [hrmul, Real.one_lt_goldenRatio, hr0]
  have hrle1 : goldenRatio⁻¹ ≤ 1 := le_of_lt hrlt1
  have hmono : goldenRatio⁻¹ ^ (n + 1) ≤ goldenRatio⁻¹ ^ 2 := by
    exact pow_le_pow_of_le_one hr0 hrle1 (by omega : 2 ≤ n + 1)
  have hφsq : (2 : ℝ) < goldenRatio ^ 2 := by
    rw [Real.goldenRatio_sq]
    linarith [Real.one_lt_goldenRatio]
  have hsq : goldenRatio⁻¹ ^ 2 < (1 : ℝ) / 2 := by
    calc
      goldenRatio⁻¹ ^ 2 = 1 / goldenRatio ^ 2 := by
        rw [inv_pow, one_div]
      _ < 1 / (2 : ℝ) := one_div_lt_one_div_of_lt (by norm_num) hφsq
  exact lt_of_le_of_lt hmono hsq

/-- 对 `n ≥ 1`, `F_n` 处的 Fibonacci 黄金倍数距离小于半个整数格。 -/
theorem fib_dist_lt_half {n : ℕ} (hn : 1 ≤ n) :
    |(Nat.fib (n + 1) : ℝ) / goldenRatio - (Nat.fib n : ℝ)| < (1 : ℝ) / 2 := by
  rw [fib_dist_to_int]
  exact goldenRatio_inv_pow_lt_half hn

end UnifiedTheory
