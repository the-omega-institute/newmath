import UnifiedTheory.Golden.GoldenWeight
import UnifiedTheory.Golden.GoldenWeightPrimeEdge
import UnifiedTheory.Golden.GoldenWeightBounds
import UnifiedTheory.Golden.DeficitSharp
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.Log.Base

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

/-- **金权生成函数非完全积性**:金权在非互素处不可加(`S 2 = 3 ≠ 2·S 1 = 4`),故局部欧拉
因子非几何、金权 L-级数不塌为 ζ 的位移/幂。见证 `x=2, m=n=2`:
`goldGenAF 2 (2*2) = 2^{S 2} = 8`,而 `goldGenAF 2 2 * goldGenAF 2 2 = (2^{S 1})² = 16`。 -/
theorem goldGenAF_not_completelyMultiplicative :
    ∃ (x : ℝ) (m n : ℕ), goldGenAF x (m * n) ≠ goldGenAF x m * goldGenAF x n := by
  refine ⟨2, 2, 2, ?_⟩
  have hleft : goldGenAF (2 : ℝ) (2 * 2) = 8 := by
    have h4 : (2 * 2 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4, goldGenAF_prime_pow (2 : ℝ) Nat.prime_two 2, S_at2]
    rw [show (3 : ℤ).toNat = 3 by rfl]
    norm_num
  have hright : goldGenAF (2 : ℝ) 2 * goldGenAF (2 : ℝ) 2 = 16 := by
    have h1 : (2 : ℕ) = 2 ^ 1 := by norm_num
    rw [h1, goldGenAF_prime_pow (2 : ℝ) Nat.prime_two 1, S_at1]
    rw [show (2 : ℤ).toNat = 2 by rfl]
    norm_num
  rw [hleft, hright]
  norm_num

/-- `2^{Ω(n)} ≤ n`:`2^{∑_p v_p} = ∏_p 2^{v_p} ≤ ∏_p p^{v_p} = n`(各素 `p ≥ 2`)。 -/
theorem two_pow_omega_le (n : ℕ) (hn : n ≠ 0) :
    2 ^ (∑ p ∈ n.factorization.support, n.factorization p) ≤ n := by
  calc 2 ^ (∑ p ∈ n.factorization.support, n.factorization p)
      = ∏ p ∈ n.factorization.support, 2 ^ n.factorization p := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ p ∈ n.factorization.support, p ^ n.factorization p := by
        apply Finset.prod_le_prod'
        intro p hp
        exact Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _
    _ = n := Nat.factorization_prod_pow_eq_self hn

/-- **金权 L-级数收敛横标界**:`x ≥ 1` 时金权生成 Dirichlet 级数 `∑ x^{Ωφ(n)} n^{-s}` 之
绝对收敛横标 `≤ 1 + 2 log₂ x`。系数界 `x^{Ωφ(n)} ≤ n^{2 log₂ x}`,经已机检 `Ωφ ≤ 2Ω`、
`Ω ≤ log₂ n`(`2^Ω ≤ n`)、rpow 底-指交换 `x^{2 log₂ n} = n^{2 log₂ x}`。 -/
theorem goldGenAF_abscissaOfAbsConv_le (x : ℝ) (hx : 1 ≤ x) :
    LSeries.abscissaOfAbsConv (fun n => (goldGen x n : ℂ))
      ≤ (1 + 2 * Real.logb 2 x : ℝ) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  refine LSeriesSummable_of_le_const_mul_rpow (x := 1 + 2 * Real.logb 2 x)
    (by exact_mod_cast hy) ⟨1, fun n hn => ?_⟩
  set Ω : ℕ := ∑ p ∈ n.factorization.support, n.factorization p with hΩ
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hk2 : ((goldWeight n).toNat : ℝ) ≤ 2 * (Ω : ℝ) := by
    have hle : goldWeight n ≤ 2 * (Ω : ℤ) := by
      have h := goldWeight_le_two_mul n
      simpa [hΩ, Nat.cast_sum] using h
    have h2 : (goldWeight n).toNat ≤ 2 * Ω := by
      have := Int.toNat_le_toNat hle
      simpa using this
    calc ((goldWeight n).toNat : ℝ) ≤ ((2 * Ω : ℕ) : ℝ) := by exact_mod_cast h2
      _ = 2 * (Ω : ℝ) := by push_cast; ring
  have hΩlog : (Ω : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos, Real.rpow_natCast]
    exact_mod_cast two_pow_omega_le n hn
  have hswap : x ^ (2 * Real.logb 2 (n : ℝ)) = (n : ℝ) ^ (2 * Real.logb 2 x) := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hnpos, Real.logb, Real.logb]
    ring_nf
  have hgn : ‖(goldGen x n : ℂ)‖ = x ^ (goldWeight n).toNat := by
    rw [goldGen, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hgn, one_mul]
  have hexp : (1 + 2 * Real.logb 2 x) - 1 = 2 * Real.logb 2 x := by ring
  rw [hexp]
  calc x ^ (goldWeight n).toNat
      = x ^ ((goldWeight n).toNat : ℝ) := (Real.rpow_natCast x _).symm
    _ ≤ x ^ (2 * (Ω : ℝ)) := Real.rpow_le_rpow_of_exponent_le hx hk2
    _ ≤ x ^ (2 * Real.logb 2 (n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    _ = (n : ℝ) ^ (2 * Real.logb 2 x) := hswap

end UnifiedTheory
