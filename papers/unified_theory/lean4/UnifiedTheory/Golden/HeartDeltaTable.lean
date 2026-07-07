import Mathlib

namespace UnifiedTheory

open Filter Topology
open scoped BigOperators

/-- **心脏 δ-表通项**(源 6.147):`δ_k = fib(k+1)·φ^{−(k+2)}`。 -/
noncomputable def heartDelta (k : ℕ) : ℝ :=
  (Nat.fib (k + 1) : ℝ) / Real.goldenRatio ^ (k + 2)

/-- `δ_0 = 1/φ²`(表首,sanity)。 -/
theorem heartDelta_zero : heartDelta 0 = 1 / Real.goldenRatio ^ 2 := by
  simp [heartDelta]

/-- **r̄-链闭值(源 6.147,一页代数)**:`Σ_{k} ψ^k δ_k = 1/(2φ)`,故 `r̄ = −1/(2φ)`。
Binet 把和拆成两条几何级数:`ψ^k δ_k = (1/√5)((1/φ)ψ^k − (ψ/φ²)ρ^k)`,`ρ = ψ²/φ = φ^{−3}`。
最终代数收束到 `1/φ + 1/φ² = 1`(即 `φ² = φ+1`)。 -/
theorem rbar_series_eq :
    ∑' k : ℕ, Real.goldenConj ^ k * heartDelta k = 1 / (2 * Real.goldenRatio) := by
  have hφpos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hφne : Real.goldenRatio ≠ 0 := ne_of_gt hφpos
  have hφ1 : (1 : ℝ) < Real.goldenRatio := Real.one_lt_goldenRatio
  have h5 : Real.sqrt 5 ≠ 0 := by positivity
  -- ψ = -(1/φ)
  have hψ : Real.goldenConj = -(1 / Real.goldenRatio) := by
    rw [Real.goldenConj, Real.goldenRatio]
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h5nz : (1 : ℝ) + Real.sqrt 5 ≠ 0 := by positivity
    field_simp
    nlinarith [h5, Real.sqrt_nonneg 5]
  -- 1 - ψ = φ
  have h1subψ : 1 - Real.goldenConj = Real.goldenRatio := by
    have h := Real.goldenRatio_add_goldenConj
    linarith
  -- √5 = 2φ - 1
  have hsqrt5 : Real.sqrt 5 = 2 * Real.goldenRatio - 1 := by
    rw [Real.goldenRatio]; ring
  -- ψ² = 1/φ²
  have hψsq : Real.goldenConj ^ 2 = 1 / Real.goldenRatio ^ 2 := by
    rw [hψ]; field_simp
  -- 1 - ψ²/φ = 2/φ²
  have h1subρ : 1 - Real.goldenConj ^ 2 / Real.goldenRatio = 2 / Real.goldenRatio ^ 2 := by
    rw [hψsq]; field_simp
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  -- norms
  have hψnorm : ‖Real.goldenConj‖ < 1 := by
    rw [Real.norm_eq_abs, hψ, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.goldenRatio)]
    rw [div_lt_one hφpos]; exact hφ1
  have hρpos : (0 : ℝ) < Real.goldenConj ^ 2 / Real.goldenRatio := by
    rw [hψsq]; positivity
  have hρnorm : ‖Real.goldenConj ^ 2 / Real.goldenRatio‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hρpos]
    have hpos : (0 : ℝ) < 2 / Real.goldenRatio ^ 2 := by positivity
    linarith [h1subρ, hpos]
  -- pointwise Binet split
  have hpt : ∀ k : ℕ, Real.goldenConj ^ k * heartDelta k
      = (1 / Real.sqrt 5) * ((1 / Real.goldenRatio) * Real.goldenConj ^ k
          - (Real.goldenConj / Real.goldenRatio ^ 2) * (Real.goldenConj ^ 2 / Real.goldenRatio) ^ k) := by
    intro k
    unfold heartDelta
    rw [Real.coe_fib_eq (k + 1)]
    have e1 : Real.goldenRatio ^ (k + 1) = Real.goldenRatio ^ k * Real.goldenRatio := by rw [pow_succ]
    have e2 : Real.goldenRatio ^ (k + 2) = Real.goldenRatio ^ k * Real.goldenRatio ^ 2 := by rw [pow_add]
    have e3 : Real.goldenConj ^ (k + 1) = Real.goldenConj ^ k * Real.goldenConj := by rw [pow_succ]
    have e4 : (Real.goldenConj ^ 2 / Real.goldenRatio) ^ k
        = Real.goldenConj ^ k * Real.goldenConj ^ k / Real.goldenRatio ^ k := by
      rw [div_pow, sq, mul_pow]
    rw [e1, e2, e3, e4]
    have ha : Real.goldenRatio ^ k ≠ 0 := pow_ne_zero _ hφne
    field_simp
  -- summability of the two geometric families
  have hf1sum : Summable (fun k : ℕ => (1 / Real.goldenRatio) * Real.goldenConj ^ k) :=
    (summable_geometric_of_norm_lt_one hψnorm).mul_left _
  have hf2sum : Summable (fun k : ℕ =>
      (Real.goldenConj / Real.goldenRatio ^ 2) * (Real.goldenConj ^ 2 / Real.goldenRatio) ^ k) :=
    (summable_geometric_of_norm_lt_one hρnorm).mul_left _
  -- assemble
  rw [tsum_congr hpt, tsum_mul_left, hf1sum.tsum_sub hf2sum,
      tsum_mul_left, tsum_mul_left,
      tsum_geometric_of_norm_lt_one hψnorm, tsum_geometric_of_norm_lt_one hρnorm,
      h1subψ, h1subρ, hψ, hsqrt5]
  rw [Real.goldenRatio]
  have hfin5nz : (1 : ℝ) + Real.sqrt 5 ≠ 0 := by positivity
  have hfin5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  field_simp
  linear_combination (-1 : ℝ) * hfin5

/-- r̄ = −1/(2φ) 显式(源 6.147 主常数之一)。 -/
theorem rbar_eq_neg :
    -(∑' k : ℕ, Real.goldenConj ^ k * heartDelta k) = -(1 / (2 * Real.goldenRatio)) := by
  rw [rbar_series_eq]

end UnifiedTheory
