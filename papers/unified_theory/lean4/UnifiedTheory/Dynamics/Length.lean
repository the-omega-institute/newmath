import UnifiedTheory.Arithmetic.PrimeAxes
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# ch18.6 长度读数 `L(a) = Σ aₚ log p`

素轴指数向量的长度读数:每轴指数乘该素数的对数之和。这是生成层成本(定理 18.7 对数版:
非平凡态长度严格正)以及相位读数 `Φ_s(a)=exp(-s·L(a))`(ch19)与热迹 `Z_K(s)=Σ exp(-s·L)`
(ch22)的公共地基。此处只给素轴态 `PrimeExp` 上的长度与其正性,不预设任何解析延拓。
-/

namespace UnifiedTheory

open scoped BigOperators

/-- 长度读数 `L(a) = Σ_p a_p · log p`(定义 18.6)。素轴指数向量到实数的对数长度。 -/
noncomputable def L (a : PrimeExp) : ℝ := a.val.sum (fun p k => (k : ℝ) * Real.log p)

/-- 每项非负(支撑上 `p` 为素数,`log p ≥ 0`),故长度非负。 -/
theorem L_nonneg (a : PrimeExp) : 0 ≤ L a := by
  simp only [L, Finsupp.sum]
  apply Finset.sum_nonneg
  intro p hp
  have hprime : Nat.Prime p := a.property p hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
  exact mul_nonneg (by positivity) hlog

/-- **定理 18.7(对数长度版)**:非平凡素轴态(指数向量非零)长度严格正。 -/
theorem L_pos (a : PrimeExp) (h : a.val ≠ 0) : 0 < L a := by
  simp only [L, Finsupp.sum]
  apply Finset.sum_pos
  · intro p hp
    have hprime : Nat.Prime p := a.property p hp
    have hk : a.val p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hkpos : (0 : ℝ) < (a.val p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hprime.one_lt)
    exact mul_pos hkpos hlog
  · exact Finsupp.support_nonempty_iff.mpr h

end UnifiedTheory
