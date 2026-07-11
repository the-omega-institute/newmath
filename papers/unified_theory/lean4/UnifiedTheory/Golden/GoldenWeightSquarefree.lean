import UnifiedTheory.Golden.GoldenWeight
import UnifiedTheory.Golden.GoldenWeightLSeries
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic

namespace UnifiedTheory

open scoped BigOperators

/-- 辅助:`v ≥ 1 ⟹ S v ≥ 2`(`S 1 = 2`,`S` 单调)。 -/
theorem two_le_S_of_one_le {v : ℕ} (hv : 1 ≤ v) : (2 : ℤ) ≤ S v := by
  calc (2 : ℤ) = S 1 := S_at1.symm
    _ ≤ S v := S_mono hv

/-- 辅助:`S v = 2 ↔ v = 1`(`S` 严格单调 ⟹ 单射,`S 1 = 2`)。 -/
theorem S_eq_two_iff {v : ℕ} : S v = 2 ↔ v = 1 := by
  constructor
  · intro h
    exact S_strictMono.injective (by rw [h, S_at1])
  · intro h
    rw [h, S_at1]

private theorem two_mul_card_eq_sum_const_two (s : Finset ℕ) :
    (2 * s.card : ℤ) = ∑ _p ∈ s, (2 : ℤ) := by
  rw [Finset.sum_const, nsmul_eq_mul]
  ring_nf

/-- **金权下界 `2·ω(n) ≤ Ωφ(n)`**(每个素因子贡献 `S(v_p) ≥ 2`)。 -/
theorem two_mul_primeFactors_card_le_goldWeight {n : ℕ} (hn : n ≠ 0) :
    (2 * n.primeFactors.card : ℤ) ≤ goldWeight n := by
  by_cases hzero : n = 0
  · exact (hn hzero).elim
  rw [goldWeight_eq_sum_of_subset (n := n) (s := n.factorization.support) (by intro p hp; exact hp)]
  change (2 * n.factorization.support.card : ℤ) ≤
    ∑ p ∈ n.factorization.support, S (n.factorization p)
  rw [two_mul_card_eq_sum_const_two]
  exact Finset.sum_le_sum fun p hp => by
    have hv_ne : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    exact two_le_S_of_one_le (Nat.one_le_iff_ne_zero.mpr hv_ne)

/-- **金权检测无平方因子性**:`Ωφ(n) = 2·ω(n) ↔ n squarefree`(等号 ⟺ 每个指数 =1)。 -/
theorem goldWeight_eq_two_mul_primeFactors_card_iff_squarefree {n : ℕ} (hn : n ≠ 0) :
    goldWeight n = 2 * n.primeFactors.card ↔ Squarefree n := by
  constructor
  · intro h
    rw [Nat.squarefree_iff_factorization_le_one hn]
    have hsum :
        (∑ p ∈ n.factorization.support, S (n.factorization p))
          = ∑ _p ∈ n.factorization.support, (2 : ℤ) := by
      have h' := h
      rw [goldWeight_eq_sum_of_subset
        (n := n) (s := n.factorization.support) (by intro p hp; exact hp)] at h'
      change (∑ p ∈ n.factorization.support, S (n.factorization p))
        = (2 * n.factorization.support.card : ℤ) at h'
      rw [two_mul_card_eq_sum_const_two] at h'
      exact h'
    have hdiff_sum :
        (∑ p ∈ n.factorization.support, (S (n.factorization p) - 2)) = 0 := by
      rw [Finset.sum_sub_distrib, hsum]
      ring
    have hdiff_nonneg :
        ∀ p ∈ n.factorization.support, 0 ≤ S (n.factorization p) - 2 := by
      intro p hp
      have hv_ne : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
      have hle := two_le_S_of_one_le (Nat.one_le_iff_ne_zero.mpr hv_ne)
      omega
    have hdiff_zero :
        ∀ p ∈ n.factorization.support, S (n.factorization p) - 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hdiff_nonneg).mp hdiff_sum
    intro p
    by_cases hp : p ∈ n.factorization.support
    · have hS : S (n.factorization p) = 2 := by
        have hz := hdiff_zero p hp
        omega
      have hv : n.factorization p = 1 := S_eq_two_iff.mp hS
      omega
    · have hv : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
      omega
  · intro hsq
    have hfac_le : ∀ p, n.factorization p ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hn).mp hsq
    rw [goldWeight_eq_sum_of_subset (n := n) (s := n.factorization.support) (by intro p hp; exact hp)]
    change (∑ p ∈ n.factorization.support, S (n.factorization p))
      = (2 * n.factorization.support.card : ℤ)
    rw [two_mul_card_eq_sum_const_two]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hv_ne : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hv_ge : 1 ≤ n.factorization p := Nat.one_le_iff_ne_zero.mpr hv_ne
    have hv : n.factorization p = 1 := le_antisymm (hfac_le p) hv_ge
    rw [hv, S_at1]

/-- **素数幂上金权 =2 ⟺ 是素数**:`IsPrimePow n ⟹ (Ωφ(n) = 2 ↔ n.Prime)`。 -/
theorem isPrimePow_goldWeight_eq_two_iff_prime {n : ℕ} (hn : IsPrimePow n) :
    goldWeight n = 2 ↔ Nat.Prime n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  rw [goldWeight_prime_pow hp]
  constructor
  · intro h
    have hk1 : k = 1 := S_eq_two_iff.mp h
    rw [hk1, pow_one]
    exact hp
  · intro hprime
    have hk1 : k = 1 := hprime.eq_one_of_pow
    rw [hk1, S_at1]

/-- 辅助:`S v = 3 ↔ v = 2`。 -/
theorem S_eq_three_iff {v : ℕ} : S v = 3 ↔ v = 2 := by
  constructor
  · intro h
    exact S_strictMono.injective (by rw [h, S_at2])
  · intro h
    rw [h, S_at2]

/-- **金权 3 检测素数平方**:`Ωφ(n) = 3 ↔ n = p²`(某素数 p)。 -/
theorem goldWeight_eq_three_iff_prime_sq {n : ℕ} (hn : n ≠ 0) :
    goldWeight n = 3 ↔ ∃ p : ℕ, Nat.Prime p ∧ n = p ^ 2 := by
  constructor
  · intro hgold
    have hcard_bound_int : (2 * n.primeFactors.card : ℤ) ≤ 3 := by
      simpa [hgold] using two_mul_primeFactors_card_le_goldWeight (n := n) hn
    have hcard_le : n.primeFactors.card ≤ 1 := by
      omega
    have hcard_ne_zero : n.primeFactors.card ≠ 0 := by
      intro hcard0
      have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard0
      have hn01 : n = 0 ∨ n = 1 := Nat.primeFactors_eq_empty.mp hempty
      cases hn01 with
      | inl h0 => exact hn h0
      | inr h1 =>
          have hzero : goldWeight n = 0 := by
            rw [h1, goldWeight_one]
          omega
    have hcard_eq : n.primeFactors.card = 1 := by
      have hcard_pos : 0 < n.primeFactors.card := Nat.pos_of_ne_zero hcard_ne_zero
      omega
    have hn_pp : IsPrimePow n := isPrimePow_iff_card_primeFactors_eq_one.mpr hcard_eq
    obtain ⟨p, k, hp, _hk, hpk⟩ := (isPrimePow_nat_iff n).mp hn_pp
    have hS : S k = 3 := by
      have hgold_pk : goldWeight (p ^ k) = 3 := by
        rw [hpk]
        exact hgold
      rwa [goldWeight_prime_pow hp] at hgold_pk
    have hk2 : k = 2 := S_eq_three_iff.mp hS
    refine ⟨p, hp, ?_⟩
    rw [← hpk, hk2]
  · rintro ⟨p, hp, rfl⟩
    rw [goldWeight_prime_pow hp, S_at2]

end UnifiedTheory
