import UnifiedTheory.Golden.GoldenWeight
import UnifiedTheory.SelfCode.GodelVec

/-!
# 定长 Gödel 向量码的金权重闭式

定长 Gödel 向量码的金权重只读取坐标指数,不依赖所选素数的具体数值。
-/

namespace UnifiedTheory.SelfCode

open scoped BigOperators
open UnifiedTheory

/-- 定长 Gödel 码 `Gvec p x = ∏ (p i)^(x i+1)` 的金权重是坐标局部且素值无关的闭式
`∑_i S(x_i+1)`——排除具体素数选择带来的 off-axis 干扰。 -/
theorem goldWeight_Gvec {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (x : Fin k → ℕ) :
    goldWeight (Gvec p x) = ∑ i, S (x i + 1) := by
  let s : Finset ℕ := Finset.univ.image p
  have hsub : (Gvec p x).factorization.support ⊆ s := by
    intro q hq
    rw [Finsupp.mem_support_iff] at hq
    by_contra hnot
    have hnot_coord : ∀ i, p i ≠ q := by
      intro i hiq
      exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hiq⟩)
    have hsum_zero : (∑ i, (if p i = q then x i + 1 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [hnot_coord i]
    exact hq (by rw [Gvec_factorization_apply p hp x q, hsum_zero])
  rw [goldWeight_eq_sum_of_subset (n := Gvec p x) (s := s) hsub]
  have hinj_on : Set.InjOn p (Finset.univ : Finset (Fin k)) := by
    intro i _ j _ hij
    exact hinj hij
  rw [Finset.sum_image hinj_on]
  apply Finset.sum_congr rfl
  intro i _
  rw [Gvec_factorization_coord p hp hinj x i]

end UnifiedTheory.SelfCode
