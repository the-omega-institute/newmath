import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace UnifiedTheory

open Real

/-- 对数坐标 `u_K = -xφ^{K+1} + yψ^{K+1}`(6.36 迹映射对数层)。 -/
noncomputable def uCoord (x y : ℝ) (K : ℕ) : ℝ :=
  -x * Real.goldenRatio ^ (K + 1) + y * Real.goldenConj ^ (K + 1)

/-- 二次型 `Q(a,b) = a² - ab - b²`(Cassini-Fricke 型)。 -/
def qForm (a b : ℝ) : ℝ := a ^ 2 - a * b - b ^ 2

/-- **定理 6.36(Cassini-Fricke 反不变量)**:
`Q(u_{K+1}, u_K) = 5xy(-1)^{K+1}`。 -/
theorem cassini_fricke (x y : ℝ) (K : ℕ) :
    qForm (uCoord x y (K + 1)) (uCoord x y K) = 5 * x * y * (-1) ^ (K + 1) := by
  unfold qForm uCoord
  have hphi_step : Real.goldenRatio ^ ((K + 1) + 1) =
      Real.goldenRatio ^ (K + 1) * Real.goldenRatio := by
    rw [pow_succ]
  have hpsi_step : Real.goldenConj ^ ((K + 1) + 1) =
      Real.goldenConj ^ (K + 1) * Real.goldenConj := by
    rw [pow_succ]
  have hpq : Real.goldenRatio ^ (K + 1) * Real.goldenConj ^ (K + 1) =
      (-1 : ℝ) ^ (K + 1) := by
    rw [← mul_pow, Real.goldenRatio_mul_goldenConj]
  rw [hphi_step, hpsi_step]
  have hphi0 : Real.goldenRatio ^ 2 - Real.goldenRatio - 1 = 0 := by
    nlinarith [Real.goldenRatio_sq]
  have hpsi0 : Real.goldenConj ^ 2 - Real.goldenConj - 1 = 0 := by
    nlinarith [Real.goldenConj_sq]
  have hcross :
      -2 * Real.goldenRatio * Real.goldenConj + Real.goldenRatio + Real.goldenConj + 2 = 5 := by
    nlinarith [Real.goldenRatio_mul_goldenConj, Real.goldenRatio_add_goldenConj]
  calc
    (-x * (Real.goldenRatio ^ (K + 1) * Real.goldenRatio)
          + y * (Real.goldenConj ^ (K + 1) * Real.goldenConj)) ^ 2
        - (-x * (Real.goldenRatio ^ (K + 1) * Real.goldenRatio)
            + y * (Real.goldenConj ^ (K + 1) * Real.goldenConj))
          * (-x * Real.goldenRatio ^ (K + 1) + y * Real.goldenConj ^ (K + 1))
        - (-x * Real.goldenRatio ^ (K + 1) + y * Real.goldenConj ^ (K + 1)) ^ 2
        = x ^ 2 * (Real.goldenRatio ^ (K + 1)) ^ 2
            * (Real.goldenRatio ^ 2 - Real.goldenRatio - 1)
          + y ^ 2 * (Real.goldenConj ^ (K + 1)) ^ 2
            * (Real.goldenConj ^ 2 - Real.goldenConj - 1)
          + x * y * (Real.goldenRatio ^ (K + 1) * Real.goldenConj ^ (K + 1))
            * (-2 * Real.goldenRatio * Real.goldenConj + Real.goldenRatio + Real.goldenConj + 2) := by
            ring
    _ = 5 * x * y * (-1) ^ (K + 1) := by
      rw [hphi0, hpsi0, hcross, hpq]
      ring

/-- **生成式推论(迹映射非退化)**:Cassini–Fricke 不变量非零 ⟺ `x ≠ 0 ∧ y ≠ 0`。
即迹映射轨道停留在退化轨迹 `xy=0` 之外当且仅当两坐标都非零——对应 Fibonacci 哈密顿量的
有界轨道/谱在非平凡参数上不塌缩。源文档未列此非退化判据。 -/
theorem cassini_fricke_ne_zero (x y : ℝ) (K : ℕ) :
    qForm (uCoord x y (K + 1)) (uCoord x y K) ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 := by
  rw [cassini_fricke]
  have hpow : ((-1 : ℝ)) ^ (K + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  constructor
  · intro h
    exact ⟨fun hx => h (by rw [hx]; ring), fun hy => h (by rw [hy]; ring)⟩
  · rintro ⟨hx, hy⟩
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hx) hy) hpow

end UnifiedTheory
