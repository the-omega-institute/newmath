import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# ch14 定长 PZG-Gödel 码是格嵌入(oracle 建议,certified)

固定 `k` 个不同素数 `p : Fin k → ℕ`,定长 Gödel 编码 `Gvec x = ∏_i (p i)^{x i + 1}`。它不仅
单射,还是从坐标序 `(Fin k → ℕ, ≤)` 到 `(ℕ⁺, ∣)` 的**格嵌入**:整除对应逐坐标 `≤`,gcd/lcm
对应逐坐标 min/max。这把自编码的"码≠数"结构升级为完整的格同态。本结果由旁路 oracle 提议,
本地机器核验。
-/

namespace UnifiedTheory.SelfCode

open scoped BigOperators

variable {k : ℕ} (p : Fin k → ℕ)

/-- 定长 Gödel 向量码 `∏_i (p i)^{x i + 1}`。 -/
def Gvec (x : Fin k → ℕ) : ℕ := ∏ i, (p i) ^ (x i + 1)

variable (hp : ∀ i, (p i).Prime)
include hp

theorem Gvec_pos (x : Fin k → ℕ) : 0 < Gvec p x :=
  Nat.pos_of_ne_zero <| by
    unfold Gvec
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).pos.ne')

/-- 一般素数 `q` 处的指数读出。 -/
theorem Gvec_factorization_apply (x : Fin k → ℕ) (q : ℕ) :
    (Gvec p x).factorization q = ∑ i, (if p i = q then x i + 1 else 0) := by
  unfold Gvec
  rw [Nat.factorization_prod (fun i _ => pow_ne_zero _ (hp i).pos.ne')]
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hp i).factorization_pow, Finsupp.single_apply]

variable (hinj : Function.Injective p)
include hinj

/-- 坐标恢复:第 `j` 个素数处的指数恰为 `x j + 1`。 -/
theorem Gvec_factorization_coord (x : Fin k → ℕ) (j : Fin k) :
    (Gvec p x).factorization (p j) = x j + 1 := by
  rw [Gvec_factorization_apply p hp]
  have : (∑ i, if p i = p j then x i + 1 else 0)
      = ∑ i, if i = j then x i + 1 else 0 := by
    apply Finset.sum_congr rfl; intro i _; simp only [hinj.eq_iff]
  rw [this, Finset.sum_ite_eq' Finset.univ j (fun i => x i + 1)]
  simp

/-- **oracle-suggested(整除 = 逐坐标 ≤)**:`Gvec x ∣ Gvec y ↔ ∀ i, x i ≤ y i`。 -/
theorem Gvec_dvd_iff (x y : Fin k → ℕ) :
    Gvec p x ∣ Gvec p y ↔ ∀ i, x i ≤ y i := by
  rw [← Nat.factorization_le_iff_dvd (Gvec_pos p hp x).ne' (Gvec_pos p hp y).ne', Finsupp.le_def]
  constructor
  · intro h i
    have := h (p i)
    rw [Gvec_factorization_coord p hp hinj, Gvec_factorization_coord p hp hinj] at this
    omega
  · intro h q
    rw [Gvec_factorization_apply p hp, Gvec_factorization_apply p hp]
    apply Finset.sum_le_sum
    intro i _
    by_cases hpq : p i = q
    · simp only [hpq, if_true]; exact Nat.add_le_add_right (h i) 1
    · simp [hpq]

/-- **oracle-suggested(gcd = 逐坐标 min)**。 -/
theorem Gvec_gcd (x y : Fin k → ℕ) :
    Nat.gcd (Gvec p x) (Gvec p y) = Gvec p (fun i => min (x i) (y i)) := by
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_ne_zero_left (Gvec_pos p hp x).ne') (Gvec_pos p hp _).ne'
  intro q
  rw [Nat.factorization_gcd (Gvec_pos p hp x).ne' (Gvec_pos p hp y).ne', Finsupp.inf_apply]
  by_cases hq : ∃ j, p j = q
  · obtain ⟨j, rfl⟩ := hq
    rw [Gvec_factorization_coord p hp hinj, Gvec_factorization_coord p hp hinj,
        Gvec_factorization_coord p hp hinj]
    omega
  · push_neg at hq
    rw [Gvec_factorization_apply p hp, Gvec_factorization_apply p hp,
        Gvec_factorization_apply p hp]
    rw [Finset.sum_eq_zero (fun i _ => if_neg (hq i)),
        Finset.sum_eq_zero (fun i _ => if_neg (hq i)),
        Finset.sum_eq_zero (fun i _ => if_neg (hq i))]
    simp

/-- **oracle-suggested(lcm = 逐坐标 max)**。 -/
theorem Gvec_lcm (x y : Fin k → ℕ) :
    Nat.lcm (Gvec p x) (Gvec p y) = Gvec p (fun i => max (x i) (y i)) := by
  apply Nat.eq_of_factorization_eq
    (Nat.lcm_ne_zero (Gvec_pos p hp x).ne' (Gvec_pos p hp y).ne') (Gvec_pos p hp _).ne'
  intro q
  rw [Nat.factorization_lcm (Gvec_pos p hp x).ne' (Gvec_pos p hp y).ne', Finsupp.sup_apply]
  by_cases hq : ∃ j, p j = q
  · obtain ⟨j, rfl⟩ := hq
    rw [Gvec_factorization_coord p hp hinj, Gvec_factorization_coord p hp hinj,
        Gvec_factorization_coord p hp hinj]
    omega
  · push_neg at hq
    rw [Gvec_factorization_apply p hp, Gvec_factorization_apply p hp,
        Gvec_factorization_apply p hp]
    rw [Finset.sum_eq_zero (fun i _ => if_neg (hq i)),
        Finset.sum_eq_zero (fun i _ => if_neg (hq i)),
        Finset.sum_eq_zero (fun i _ => if_neg (hq i))]
    simp

end UnifiedTheory.SelfCode
