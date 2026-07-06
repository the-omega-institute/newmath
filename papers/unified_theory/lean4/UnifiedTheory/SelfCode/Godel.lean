import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.List.Basic

/-!
# ch14.1 PZG-Gödel 序列编码(自代码层自指基建)

用前若干素数的幂编码有限序列:`godelEncode l = ∏_{i<len} p_i^{l_i+1}`(`p_i` = 第 i 个素数,
`+1` 保证每位都出现)。核心:编码**单射**——不同序列得不同码——这是自编码不可穷尽
(配合 Cantor 对角 16.2/16.3)的算术基建。
-/

namespace UnifiedTheory.SelfCode

/-- 第 i 个素数。 -/
noncomputable def prm (i : ℕ) : ℕ := Nat.nth Nat.Prime i

theorem prm_prime (i : ℕ) : (prm i).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i

theorem prm_injective : Function.Injective prm :=
  Nat.nth_injective Nat.infinite_setOf_prime

/-- PZG-Gödel 编码:`∏_{i<len} p_i^{l_i+1}`。 -/
noncomputable def godelEncode (l : List ℕ) : ℕ :=
  ∏ i ∈ Finset.range l.length, (prm i) ^ (l.getD i 0 + 1)

/-- 编码在第 j 个素数处的指数读出序列项:`= (l_j+1) if j<len else 0`。 -/
theorem godel_factorization (l : List ℕ) (j : ℕ) :
    (godelEncode l).factorization (prm j)
      = if j < l.length then l.getD j 0 + 1 else 0 := by
  unfold godelEncode
  rw [Nat.factorization_prod (by
    intro i _; exact pow_ne_zero _ (prm_prime i).pos.ne')]
  rw [Finsupp.finset_sum_apply]
  have hterm : ∀ i ∈ Finset.range l.length,
      ((prm i) ^ (l.getD i 0 + 1)).factorization (prm j)
        = if i = j then l.getD i 0 + 1 else 0 := by
    intro i _
    rw [(prm_prime i).factorization_pow]
    simp only [Finsupp.single_apply, prm_injective.eq_iff]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range l.length) j
    (fun i => l.getD i 0 + 1)]
  simp only [Finset.mem_range]

theorem godelEncode_injective : Function.Injective godelEncode := by
  intro l l' h
  have key : ∀ j, (if j < l.length then l.getD j 0 + 1 else 0)
      = (if j < l'.length then l'.getD j 0 + 1 else 0) := by
    intro j
    rw [← godel_factorization l j, ← godel_factorization l' j, h]
  have hlen : l.length = l'.length := by
    by_contra hne
    rcases Nat.lt_or_ge l.length l'.length with hlt | hge
    · have := key l.length
      simp only [lt_irrefl, if_false, hlt, if_true] at this
      omega
    · have hlt' : l'.length < l.length := lt_of_le_of_ne hge (Ne.symm hne)
      have := key l'.length
      simp only [lt_irrefl, if_false, hlt', if_true] at this
      omega
  apply List.ext_getElem hlen
  intro i h1 h2
  have := key i
  rw [if_pos h1, if_pos (hlen ▸ h1)] at this
  have hgd : l.getD i 0 = l'.getD i 0 := by omega
  rwa [List.getD_eq_getElem l 0 h1, List.getD_eq_getElem l' 0 h2] at hgd

end UnifiedTheory.SelfCode
