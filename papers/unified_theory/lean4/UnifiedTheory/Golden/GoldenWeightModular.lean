import UnifiedTheory.Golden.GoldenWeight

/-!
# 金权重的 gcd/lcm 模律

金权重在整除格的 meet/join 上满足精确赋值恒等式。这里的证明只使用素因子
指数向量中 gcd/lcm 分别对应逐点 inf/sup 的事实。
-/

namespace UnifiedTheory

open scoped BigOperators

/-- 金权重是整除格 `(ℕ⁺, ∣)` 上的赋值/模律:
`Ωφ(gcd m n) + Ωφ(lcm m n) = Ωφ m + Ωφ n`。与乘法拟同态
(有障碍 `κφ`) 对比, meet/join 无障碍、精确模律。 -/
theorem goldWeight_gcd_lcm_modular (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    goldWeight (Nat.gcd m n) + goldWeight (Nat.lcm m n) = goldWeight m + goldWeight n := by
  have hfacGcd : (Nat.gcd m n).factorization = m.factorization ⊓ n.factorization :=
    Nat.factorization_gcd hm hn
  have hfacLcm : (Nat.lcm m n).factorization = m.factorization ⊔ n.factorization :=
    Nat.factorization_lcm hm hn
  set s := m.factorization.support ∪ n.factorization.support with hs
  have hGoldM : goldWeight m = ∑ p ∈ s, S (m.factorization p) :=
    goldWeight_eq_sum_of_subset (n := m) (s := s) Finset.subset_union_left
  have hGoldN : goldWeight n = ∑ p ∈ s, S (n.factorization p) :=
    goldWeight_eq_sum_of_subset (n := n) (s := s) Finset.subset_union_right
  have hGoldGcd :
      goldWeight (Nat.gcd m n) =
        ∑ p ∈ s, S (m.factorization p ⊓ n.factorization p) := by
    have hsub : (Nat.gcd m n).factorization.support ⊆ s := by
      intro p hp
      rw [hfacGcd, Finsupp.mem_support_iff, Finsupp.inf_apply] at hp
      rw [Finset.mem_union]
      left
      rw [Finsupp.mem_support_iff]
      intro hpm
      exact hp (by simp [hpm])
    rw [goldWeight_eq_sum_of_subset (n := Nat.gcd m n) (s := s) hsub]
    apply Finset.sum_congr rfl
    intro p _
    rw [hfacGcd, Finsupp.inf_apply]
  have hGoldLcm :
      goldWeight (Nat.lcm m n) =
        ∑ p ∈ s, S (m.factorization p ⊔ n.factorization p) := by
    have hsub : (Nat.lcm m n).factorization.support ⊆ s := by
      intro p hp
      rw [hfacLcm, Finsupp.mem_support_iff, Finsupp.sup_apply] at hp
      rw [Finset.mem_union]
      by_cases hpm : m.factorization p = 0
      · right
        rw [Finsupp.mem_support_iff]
        intro hpn
        exact hp (by simp [hpm, hpn])
      · left
        rwa [Finsupp.mem_support_iff]
    rw [goldWeight_eq_sum_of_subset (n := Nat.lcm m n) (s := s) hsub]
    apply Finset.sum_congr rfl
    intro p _
    rw [hfacLcm, Finsupp.sup_apply]
  rw [hGoldGcd, hGoldLcm, hGoldM, hGoldN, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rcases le_total (m.factorization p) (n.factorization p) with hle | hle
  · rw [inf_eq_left.mpr hle, sup_eq_right.mpr hle]
  · rw [inf_eq_right.mpr hle, sup_eq_left.mpr hle, add_comm]

end UnifiedTheory
