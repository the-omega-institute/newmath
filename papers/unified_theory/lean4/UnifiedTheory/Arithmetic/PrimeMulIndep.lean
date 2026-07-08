import Mathlib

namespace UnifiedTheory

open Finset

/-- `padicValRat p (q:ℚ) = 0` for distinct primes. -/
theorem padicValRat_distinct_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    padicValRat p (q : ℚ) = 0 := by
  haveI := Fact.mk hp
  rw [show ((q : ℚ)) = ((q : ℤ) : ℚ) by push_cast; ring, padicValRat.of_int]
  rw [padicValInt.eq_zero_of_not_dvd]
  · rfl
  · intro hdvd
    rw [Int.natCast_dvd_natCast] at hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)

/-- `padicValRat` of an integer power: `v_q(x^n) = n·v_q(x)`. -/
theorem padicValRat_zpow {q : ℕ} [Fact q.Prime] {x : ℚ} (hx : x ≠ 0) :
    ∀ n : ℤ, padicValRat q (x ^ n) = n * padicValRat q x
  | (k : ℕ) => by rw [zpow_natCast, padicValRat.pow hx]
  | Int.negSucc k => by
      rw [zpow_negSucc, padicValRat.inv, padicValRat.pow hx, Int.negSucc_eq]
      push_cast; ring

/-- `padicValRat` of a finite product of nonzero rationals is the sum of valuations. -/
theorem padicValRat_prod {q : ℕ} [Fact q.Prime] (s : Finset ℕ) (f : ℕ → ℚ)
    (hf : ∀ p ∈ s, f p ≠ 0) :
    padicValRat q (∏ p ∈ s, f p) = ∑ p ∈ s, padicValRat q (f p) := by
  induction s using Finset.induction with
  | empty => simp [padicValRat.one]
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx,
      padicValRat.mul (hf x (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun p hp => hf p (Finset.mem_insert_of_mem hp)),
      ih fun p hp => hf p (Finset.mem_insert_of_mem hp)]

/-- **素数在 ℚˣ 中乘性独立(源 18.10 之自由部分)**:形式素指数向量 `a : ℕ →₀ ℤ`(支撑皆素)
若 `∏ p^{a_p} = 1` 于 ℚ,则 `a = 0`。即映射 `a ↦ ∏ p^{a_p}` 单射——正有理数群
在素数上自由(无关系),这是 18.10「(ℚ₊,×) 为素数轴上自由阿贝尔群」之自由半。
证法:对每个素数 `q` 取 `padicValRat q`,乘积化为和,`p ≠ q` 项因 `v_q(p)=0` 归零,
`p = q` 项给出 `a q`;而 `v_q(1) = 0` 迫使 `a q = 0`。 -/
theorem primes_mul_indep (a : ℕ →₀ ℤ) (ha : ∀ p ∈ a.support, Nat.Prime p)
    (h : (a.prod fun p n => (p : ℚ) ^ n) = 1) : a = 0 := by
  ext q
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_cases hq : q ∈ a.support
  · have hqp : q.Prime := ha q hq
    haveI := Fact.mk hqp
    have key : padicValRat q (a.prod fun p n => (p : ℚ) ^ n) = a q := by
      rw [Finsupp.prod]
      have hne : ∀ p ∈ a.support, ((p : ℚ) ^ (a p)) ≠ 0 := by
        intro p hp
        exact zpow_ne_zero _ (by exact_mod_cast (ha p hp).pos.ne')
      rw [padicValRat_prod _ _ hne]
      rw [Finset.sum_eq_single q]
      · rw [padicValRat_zpow (by exact_mod_cast hqp.pos.ne') _, padicValRat.self hqp.one_lt,
          Int.mul_one]
      · intro p hp hpq
        rw [padicValRat_zpow (by exact_mod_cast (ha p hp).pos.ne') _,
          padicValRat_distinct_prime hqp (ha p hp) (Ne.symm hpq), Int.mul_zero]
      · intro hqs; exact absurd hq hqs
    rw [h, padicValRat.one] at key
    omega
  · exact Finsupp.notMem_support_iff.mp hq

end UnifiedTheory
