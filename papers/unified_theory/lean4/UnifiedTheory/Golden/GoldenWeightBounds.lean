import UnifiedTheory.Golden.GoldenWeight

namespace UnifiedTheory

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

end UnifiedTheory
