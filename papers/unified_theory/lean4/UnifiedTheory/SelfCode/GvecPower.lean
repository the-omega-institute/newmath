import UnifiedTheory.SelfCode.GodelVec
import Mathlib

namespace UnifiedTheory.SelfCode

open scoped BigOperators

theorem gvec_isPow_iff_coord_dvd {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (e : ℕ) (he : 0 < e) (x : Fin k → ℕ) :
    (∃ m : ℕ, Gvec p x = m ^ e) ↔ ∀ i : Fin k, e ∣ x i + 1 := by
  constructor
  · rintro ⟨m, hm⟩ i
    have hfact : (Gvec p x).factorization (p i) = (m ^ e).factorization (p i) := by rw [hm]
    rw [Gvec_factorization_coord p hp hinj x i, Nat.factorization_pow, Finsupp.smul_apply] at hfact
    exact ⟨m.factorization (p i), hfact.trans (by simp)⟩
  · intro h
    refine ⟨∏ i, (p i) ^ ((x i + 1) / e), ?_⟩
    rw [Gvec, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, Nat.div_mul_cancel (h i)]

end UnifiedTheory.SelfCode
