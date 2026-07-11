import UnifiedTheory.Golden.GoldenWeight
import Mathlib

namespace UnifiedTheory

open scoped BigOperators

/-- **阶乘的金权(Legendre 显式式)**:`Ωφ(N!) = ∑_{p∈primeFactors(N!)} S(∑_{i≥1} ⌊N/p^i⌋)`,
内层是 `p` 在 `N!` 中的 Legendre 指数(截到 `⌊log_p N⌋`)。 -/
theorem goldWeight_factorial (N : ℕ) :
    goldWeight (N.factorial) = ∑ p ∈ (N.factorial).primeFactors,
      S (∑ i ∈ Finset.Ico 1 (Nat.log p N + 1), N / p ^ i) := by
  unfold goldWeight
  rw [Nat.support_factorization]
  apply Finset.sum_congr rfl
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [Nat.factorization_factorial hp_prime (Nat.lt_succ_self (Nat.log p N))]

end UnifiedTheory
