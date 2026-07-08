import UnifiedTheory.Golden.GoldenWeight
import UnifiedTheory.Golden.GoldenJump

/-!
# Golden weight prime edges

Multiplication by one prime axis changes `goldWeight` exactly by the next golden
Sturmian jump on that axis.
-/

namespace UnifiedTheory

open scoped BigOperators

private theorem factorization_prime_pow (p N : ℕ) (hp : Nat.Prime p) :
    (p ^ N).factorization = Finsupp.single p N := by
  rw [Nat.factorization_pow, Nat.Prime.factorization hp, Finsupp.smul_single]
  simp

/-- Window form for a prime-axis power: only the `p`-axis contributes to the
golden-weight increment. -/
theorem goldWeight_mul_prime_pow (p n N : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0) :
    goldWeight (p ^ N * n) - goldWeight n
      = S (n.factorization p + N) - S (n.factorization p) := by
  have hpN_ne : p ^ N ≠ 0 := pow_ne_zero N hp.ne_zero
  have hfac : (p ^ N * n).factorization = (p ^ N).factorization + n.factorization :=
    Nat.factorization_mul hpN_ne hn
  have hpow : (p ^ N).factorization = Finsupp.single p N :=
    factorization_prime_pow p N hp
  set s : Finset ℕ := insert p n.factorization.support with hs
  have hsub_n : n.factorization.support ⊆ s := by
    rw [hs]
    exact Finset.subset_insert p n.factorization.support
  have hsub_mul : (p ^ N * n).factorization.support ⊆ s := by
    intro q hq
    rw [hs]
    by_cases hqp : q = p
    · rw [hqp]
      exact Finset.mem_insert_self p n.factorization.support
    · rw [Finset.mem_insert]
      right
      rw [Finsupp.mem_support_iff]
      rw [Finsupp.mem_support_iff, hfac, hpow, Finsupp.add_apply] at hq
      have hpq : p ≠ q := fun hpq => hqp hpq.symm
      simpa [hpq] using hq
  have hWmul := goldWeight_eq_sum_of_subset (n := p ^ N * n) (s := s) hsub_mul
  have hWn := goldWeight_eq_sum_of_subset (n := n) (s := s) hsub_n
  rw [hWmul, hWn, ← Finset.sum_sub_distrib]
  have hsum :
      (∑ q ∈ s, (S ((p ^ N * n).factorization q) - S (n.factorization q)))
        = S (n.factorization p + N) - S (n.factorization p) := by
    refine (Finset.sum_eq_single
      (s := s)
      (f := fun q => S ((p ^ N * n).factorization q) - S (n.factorization q))
      p ?_ ?_).trans ?_
    · intro q _ hqne
      have hpq : p ≠ q := fun hpq => hqne hpq.symm
      have hprod : (p ^ N * n).factorization q = n.factorization q := by
        rw [hfac, hpow, Finsupp.add_apply]
        simp [hpq]
      simp [hprod]
    · intro hp_not_mem
      exact (hp_not_mem (by rw [hs]; exact Finset.mem_insert_self p n.factorization.support)).elim
    · have hpval : (p ^ N * n).factorization p = N + n.factorization p := by
        rw [hfac, hpow, Finsupp.add_apply]
        simp
      simp [hpval, Nat.add_comm]
  exact hsum

/-- 乘一个素数 `p`,金权重增量 `Ωφ(pn)−Ωφ n = 1 + goldJump(v_p n) ∈ {1,2}`,
恰由黄金 Sturmian 词决定;把「严格因子增量为正」锐化为「精确 1 或 2」。 -/
theorem goldWeight_mul_prime (p n : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0) :
    goldWeight (p * n) = goldWeight n + 1 + goldJump (n.factorization p) := by
  have hdelta : goldWeight (p * n) - goldWeight n
      = S (n.factorization p + 1) - S (n.factorization p) := by
    simpa [pow_one] using goldWeight_mul_prime_pow p n 1 hp hn
  unfold goldJump
  omega

end UnifiedTheory
