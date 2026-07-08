import UnifiedTheory.SelfCode.GodelVec
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Gödel 向量码的因子计数

固定互异素数族 `p : Fin k → ℕ` 时,`Gvec p x` 的素因子正好是坐标素数,
因子数为逐坐标指数选择数的乘积。
-/

namespace UnifiedTheory.SelfCode

open UnifiedTheory
open scoped BigOperators

theorem Gvec_primeFactors {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (x : Fin k → ℕ) :
    (Gvec p x).primeFactors = Finset.univ.image p := by
  apply Finset.Subset.antisymm
  · intro q hq
    have hq_support : q ∈ (Gvec p x).factorization.support := by
      simpa [Nat.support_factorization] using hq
    have hq_ne : (Gvec p x).factorization q ≠ 0 :=
      Finsupp.mem_support_iff.mp hq_support
    rw [Gvec_factorization_apply p hp x q] at hq_ne
    obtain ⟨i, hi_mem, hi_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq_ne
    by_cases hpiq : p i = q
    · exact Finset.mem_image.mpr ⟨i, hi_mem, hpiq⟩
    · simp [hpiq] at hi_ne
  · intro q hq
    obtain ⟨j, hj_mem, rfl⟩ := Finset.mem_image.mp hq
    have hj_support : p j ∈ (Gvec p x).factorization.support := by
      rw [Finsupp.mem_support_iff]
      rw [Gvec_factorization_coord p hp hinj x j]
      omega
    simpa [Nat.support_factorization] using hj_support

/-- **Gödel 码因子计数**:`Gvec p x` 恰有 `∏_i (x_i + 2)` 个因子。 -/
theorem Gvec_divisors_card {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (x : Fin k → ℕ) :
    (Gvec p x).divisors.card = ∏ i, (x i + 2) := by
  rw [Nat.card_divisors (Gvec_pos p hp x).ne', Gvec_primeFactors p hp hinj x]
  rw [Finset.prod_image (fun a _ b _ h => hinj h)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Gvec_factorization_coord p hp hinj x i]

end UnifiedTheory.SelfCode
