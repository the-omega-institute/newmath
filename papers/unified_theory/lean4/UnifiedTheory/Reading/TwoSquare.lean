import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# ch9 二轴范数分类(定理 9.10)

读数分类范例:以 `a²+b²`(高斯整数范数 ℚ(i))为读数的分类。**素数是两平方和 ⟺ p mod 4 ≠ 3**。
难方向(存在)是 Fermat 二平方定理(mathlib `Nat.Prime.sq_add_sq`);易方向由平方 mod 4 ∈ {0,1}。
这是同余型(值层)判定读数的典范,与第六章亏空的窗口型(码层)构成"内核之二"的虚实两面
(评注 6.29:ℚ(i) 范数 vs ℚ(√5) 亏空迹)。
-/

namespace UnifiedTheory.Reading

/-- 平方 mod 4 只能是 0 或 1。 -/
theorem sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have h : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := by rw [Nat.pow_mod]
  have hlt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [h]; interval_cases (n % 4) <;> decide

/-- 易方向:两平方和不同余 3 (mod 4)。 -/
theorem not_three_of_sq_add_sq {p a b : ℕ} (h : a ^ 2 + b ^ 2 = p) : p % 4 ≠ 3 := by
  rcases sq_mod_four a with ha | ha <;> rcases sq_mod_four b with hb | hb <;> omega

/-- **定理 9.10(二平方分类)**:素数是两平方和 ⟺ p mod 4 ≠ 3。 -/
theorem prime_sq_add_sq_iff (p : ℕ) [Fact p.Prime] :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ p % 4 ≠ 3 := by
  constructor
  · rintro ⟨a, b, hab⟩
    exact not_three_of_sq_add_sq hab
  · exact Nat.Prime.sq_add_sq

/-- **定理 9.10(一般二平方分类)**:一个自然数是两平方和,当且仅当每个
`3 mod 4` 素因子在它的分解中出现偶数次。

这是值层的完整分类:素数版 `prime_sq_add_sq_iff` 是 `n = p` 的分支,
并把第六章亏空讨论中的“二次特权”落在高斯范数 `ℚ(i)` 的可判定因子条件上,
与 `ℚ(√5)` 的窗口型亏空相对照。 -/
theorem sq_add_sq_iff_factorization (n : ℕ) :
    (∃ a b : ℕ, n = a ^ 2 + b ^ 2) ↔
      ∀ p : ℕ, p.Prime → p % 4 = 3 → Even (n.factorization p) := by
  rw [Nat.eq_sq_add_sq_iff]
  constructor
  · intro h p hp hpmod
    by_cases hmem : p ∈ n.primeFactors
    · simpa [Nat.factorization_def n hp] using h p hmem hpmod
    · have hzero : n.factorization p = 0 := by
        simpa [Nat.support_factorization] using Finsupp.notMem_support_iff.mp hmem
      simp [hzero]
  · intro h p hpmem hpmod
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    simpa [Nat.factorization_def n hp] using h p hp hpmod

end UnifiedTheory.Reading
