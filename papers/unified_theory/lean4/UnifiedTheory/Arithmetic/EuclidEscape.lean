import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# ch4 素轴不可穷尽(定理 4.5)

Euclid 逃逸数 `E_S = (∏_{p∈S} p) + 1`:对任意有限素数集 `S`,存在整除 `E_S` 的素数落在 `S` 外。
这是乘法层自身的超出定理——素数轴的 tail 由它开账(第十二章)。
-/

namespace UnifiedTheory

/-- Euclid 逃逸数:有限素数集之积加一。 -/
def euclidEscape (S : Finset ℕ) : ℕ := S.prod id + 1

/-- **定理 4.5(素轴不可穷尽)**:对任意有限素数集 `S`,存在整除逃逸数的素数不在 `S` 中。 -/
theorem exists_prime_not_mem (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    ∃ q, Nat.Prime q ∧ q ∣ euclidEscape S ∧ q ∉ S := by
  have hprod_ne : S.prod id ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => (hS p hp).pos.ne'
  have hesc_ne_one : euclidEscape S ≠ 1 := by unfold euclidEscape; omega
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hesc_ne_one
  refine ⟨q, hq_prime, hq_dvd, ?_⟩
  intro hq_mem
  have h1 : q ∣ S.prod id := Finset.dvd_prod_of_mem id hq_mem
  have h2 : q ∣ 1 := (Nat.dvd_add_right h1).mp hq_dvd
  exact hq_prime.one_lt.ne' (Nat.dvd_one.mp h2)

end UnifiedTheory
