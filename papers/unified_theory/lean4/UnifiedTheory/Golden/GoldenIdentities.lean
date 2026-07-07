import Mathlib

namespace UnifiedTheory

open Real

/-- `φ³ = 2φ + 1`。 -/
theorem goldenRatio_cube : goldenRatio ^ 3 = 2 * goldenRatio + 1 := by
  linear_combination (goldenRatio + 1) * Real.goldenRatio_sq

/-- `φ⁴ = 3φ + 2`。 -/
theorem goldenRatio_pow4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  linear_combination
    (goldenRatio ^ 2 + goldenRatio + 2) * Real.goldenRatio_sq

/-- **心脏小章一页代数(旗标恒等)**:`φ⁴ + φ² − 1 = 2φ³`。 -/
theorem goldenRatio_pow4_add_sq_sub_one :
    goldenRatio ^ 4 + goldenRatio ^ 2 - 1 = 2 * goldenRatio ^ 3 := by
  rw [goldenRatio_pow4, goldenRatio_cube, Real.goldenRatio_sq]
  ring

/-- **二阶级联黄金相消(命题 6.19)**:`φ² + φ³ = φ⁴`。 -/
theorem goldenRatio_sq_add_cube :
    goldenRatio ^ 2 + goldenRatio ^ 3 = goldenRatio ^ 4 := by
  rw [Real.goldenRatio_sq, goldenRatio_cube, goldenRatio_pow4]
  ring

/-- **Zeckendorf 禁 11 之解析影(定理 6.23)**:`φ⁴ − φ³ − φ² = 0`。 -/
theorem goldenRatio_pow4_sub_cube_sub_sq :
    goldenRatio ^ 4 - goldenRatio ^ 3 - goldenRatio ^ 2 = 0 := by
  rw [goldenRatio_pow4, goldenRatio_cube, Real.goldenRatio_sq]
  ring

/-- `ψ = −1/φ`(共轭即负倒数)。 -/
theorem goldenConj_eq_neg_inv : goldenConj = -1 / goldenRatio := by
  rw [div_eq_mul_inv, Real.inv_goldenRatio]
  ring

/-- `1/φ = φ − 1`。 -/
theorem goldenRatio_inv_eq : 1 / goldenRatio = goldenRatio - 1 := by
  rw [one_div, Real.inv_goldenRatio]
  linarith [Real.goldenRatio_add_goldenConj]

/-- **C₀ 两枚半黄金(拆分)**:`φ/2 = √5/2 − 1/(2φ)`。 -/
theorem goldenRatio_half_eq_sqrt5_half_sub :
    goldenRatio / 2 = Real.sqrt 5 / 2 - 1 / (2 * goldenRatio) := by
  have hφ : (goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hsqrt : Real.sqrt 5 = 2 * goldenRatio - 1 := by
    change Real.sqrt 5 = 2 * ((1 + Real.sqrt 5) / 2) - 1
    ring
  have hhalf_inv : 1 / (2 * goldenRatio) = (goldenRatio - 1) / 2 := by
    calc
      1 / (2 * goldenRatio) = (1 / goldenRatio) / 2 := by
        field_simp [hφ]
      _ = (goldenRatio - 1) / 2 := by
        rw [goldenRatio_inv_eq]
  rw [hhalf_inv, hsqrt]
  ring

/-- **Binet 逐位恒等(r̄-链之种,观察 6.146(二))**:`F_{k+1}/φ = F_k − ψ^{k+1}`。 -/
theorem fib_succ_div_goldenRatio (k : ℕ) :
    (Nat.fib (k + 1) : ℝ) / goldenRatio = (Nat.fib k : ℝ) - goldenConj ^ (k + 1) := by
  have hφ : (goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  have hmul : goldenRatio * goldenConj ^ (k + 1) = -goldenConj ^ k := by
    calc
      goldenRatio * goldenConj ^ (k + 1) = (goldenRatio * goldenConj) * goldenConj ^ k := by
        rw [pow_succ']
        ring
      _ = -goldenConj ^ k := by
        rw [Real.goldenRatio_mul_goldenConj]
        ring
  rw [div_eq_iff hφ]
  nlinarith [Real.fib_succ_sub_goldenRatio_mul_fib k, hmul]

/-- **c\* 恒等(钉一,源 6.145(一))**:`φ² + 1 = √5·φ`(= c\*)。 -/
theorem cstar_eq_sqrt5_phi : goldenRatio ^ 2 + 1 = Real.sqrt 5 * goldenRatio := by
  have hsqrt : Real.sqrt 5 = 2 * goldenRatio - 1 := by
    change Real.sqrt 5 = 2 * ((1 + Real.sqrt 5) / 2) - 1
    ring
  rw [hsqrt]
  nlinarith [Real.goldenRatio_sq]

end UnifiedTheory
