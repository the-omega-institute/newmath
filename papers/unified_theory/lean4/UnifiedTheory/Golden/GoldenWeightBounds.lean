import UnifiedTheory.Golden.GoldenWeight

namespace UnifiedTheory

open scoped BigOperators

/-- `S v ≤ 2v`: from `φ < 2`, `(v+1)φ < 2(v+1)`, so the floor is at most `2v+1`. -/
theorem S_le_two_mul (v : ℕ) : S v ≤ 2 * (v : ℤ) := by
  unfold S
  have hlt : ⌊((v : ℝ) + 1) * Real.goldenRatio⌋ < 2 * (v : ℤ) + 2 := by
    apply Int.floor_lt.mpr
    push_cast
    have hvpos : (0 : ℝ) < (v : ℝ) + 1 := by positivity
    nlinarith [Real.goldenRatio_lt_two, Real.goldenRatio_pos, hvpos]
  omega

/-- `v+1 ≤ S v` for `v ≥ 1`: `φ > 3/2` gives `(v+1)φ ≥ v+2`. -/
theorem succ_le_S {v : ℕ} (hv : 1 ≤ v) : (v : ℤ) + 1 ≤ S v := by
  unfold S
  have hge : (v : ℤ) + 2 ≤ ⌊((v : ℝ) + 1) * Real.goldenRatio⌋ := by
    apply Int.le_floor.mpr
    push_cast
    have hv' : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
    have hφ32 : (3 : ℝ) / 2 < Real.goldenRatio := by
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio, Real.goldenRatio_lt_two]
    nlinarith [hφ32, hv', Real.goldenRatio_pos]
  omega

/-- 金权重两侧界 `Ω+ω ≤ Ωφ ≤ 2Ω`: `S` 的两侧线性界逐项求和。 -/
theorem goldWeight_le_two_mul (n : ℕ) :
    goldWeight n ≤ 2 * ∑ p ∈ n.factorization.support, (n.factorization p : ℤ) := by
  unfold goldWeight
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun p _ => S_le_two_mul (n.factorization p))

/-- 金权重两侧界 `Ω+ω ≤ Ωφ ≤ 2Ω`: `S` 的两侧线性界逐项求和。 -/
theorem sum_succ_le_goldWeight (n : ℕ) :
    ∑ p ∈ n.factorization.support, ((n.factorization p : ℤ) + 1) ≤ goldWeight n := by
  unfold goldWeight
  apply Finset.sum_le_sum
  intro p hp
  have hpne : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hv : 1 ≤ n.factorization p := Nat.one_le_iff_ne_zero.mpr hpne
  exact succ_le_S hv

end UnifiedTheory
