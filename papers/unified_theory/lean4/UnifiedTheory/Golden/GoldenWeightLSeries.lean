import UnifiedTheory.Golden.GoldenWeight
import UnifiedTheory.Golden.GoldenWeightPrimeEdge
import Mathlib.NumberTheory.ArithmeticFunction

namespace UnifiedTheory

open ArithmeticFunction

/-- 金权生成函数的局部值 `x^{Ωφ(n)}`(`Ωφ ≥ 0`,故 `Int.toNat` 无损)。 -/
noncomputable def goldGen (x : ℝ) (n : ℕ) : ℝ := x ^ (goldWeight n).toNat

/-- 打包为 mathlib 算术函数(约定 `f 0 = 0`)。 -/
noncomputable def goldGenAF (x : ℝ) : ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else x ^ (goldWeight n).toNat
  map_zero' := by simp

theorem goldGenAF_apply (x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    goldGenAF x n = x ^ (goldWeight n).toNat := by
  simp [goldGenAF, hn]

/-- 辅助:`Ωφ(1)=0`。 -/
theorem goldWeight_one : goldWeight 1 = 0 := by
  simp [goldWeight, Nat.factorization_one]

/-- **金权生成函数是积性算术函数**(`Ωφ` 互素可加 ⇒ 生成函数积性)。 -/
theorem goldGenAF_isMultiplicative (x : ℝ) : (goldGenAF x).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · rw [goldGenAF_apply x one_ne_zero, goldWeight_one]
    simp
  · intro m n hm hn hcop
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    have hnonneg_m := goldWeight_nonneg m
    have hnonneg_n := goldWeight_nonneg n
    rw [goldGenAF_apply x hmn, goldGenAF_apply x hm, goldGenAF_apply x hn,
      goldWeight_mul_of_coprime hm hn hcop, Int.toNat_add hnonneg_m hnonneg_n,
      pow_add]

/-- 辅助:素数幂上 `Ωφ(p^v) = S v`。 -/
theorem goldWeight_prime_pow {p : ℕ} (hp : p.Prime) (v : ℕ) :
    goldWeight (p ^ v) = S v := by
  by_cases hv : v = 0
  · subst v
    rw [pow_zero, goldWeight_one, S_at0]
  · rw [goldWeight, Nat.Prime.factorization_pow hp, Finsupp.support_single_ne_zero p hv]
    simp [Finsupp.single_eq_same]

/-- **局部欧拉因子**:`goldGenAF x (p^v) = x^{S v}`(素数 p)。 -/
theorem goldGenAF_prime_pow (x : ℝ) {p : ℕ} (hp : p.Prime) (v : ℕ) :
    goldGenAF x (p ^ v) = x ^ (S v).toNat := by
  have hpv : p ^ v ≠ 0 := pow_ne_zero v hp.ne_zero
  rw [goldGenAF_apply x hpv, goldWeight_prime_pow hp v]

/-- **有限欧拉积**:`n≠0` 时金权生成函数按素因子分解为局部金因子之积。 -/
theorem goldGenAF_euler (x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    goldGenAF x n = n.factorization.prod (fun _ k => x ^ (S k).toNat) := by
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    (goldGenAF x) (goldGenAF_isMultiplicative x) hn]
  refine Finsupp.prod_congr fun p hp => ?_
  exact goldGenAF_prime_pow x (Nat.prime_of_mem_primeFactors hp) (n.factorization p)

end UnifiedTheory
