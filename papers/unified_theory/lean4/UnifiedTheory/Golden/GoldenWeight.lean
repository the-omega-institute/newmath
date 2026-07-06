import UnifiedTheory.Golden.DeficitSharp
import Mathlib.Data.Nat.Factorization.Basic

/-!
# ch4×ch6 跨层金权重拟同态(oracle 建议,certified)

金权重 `Ωφ(n) := ∑_{p ∈ supp(n)} S(n_p)`(对素数轴指数求和位移读数 `S`)。它把黄金/亏空层
(ch6)接到素数分解层(ch4):在乘法下 `Ωφ` **拟同态**,非同态障碍恰为公共素轴上的黄金亏空之和
`κφ(m,n) := ∑_p cDef(m_p, n_p)`——`Ωφ(mn) = Ωφ m + Ωφ n − κφ(m,n)`。互素时支撑不交、`κφ=0`,
故 `Ωφ` 在互素乘法上严格可加。这是黄金层与素数层的深跨层桥,本结果由旁路 oracle 提议、本地核验。
-/

namespace UnifiedTheory

open scoped BigOperators

/-- 金权重 `Ωφ(n) = ∑_{p∈supp(n)} S(n_p)`。 -/
noncomputable def goldWeight (n : ℕ) : ℤ :=
  ∑ p ∈ n.factorization.support, S (n.factorization p)

/-- 金进位障碍 `κφ(m,n) = ∑_{p∈supp(m)∪supp(n)} cDef(m_p, n_p)`。 -/
noncomputable def goldObstruction (m n : ℕ) : ℤ :=
  ∑ p ∈ m.factorization.support ∪ n.factorization.support,
    cDef (m.factorization p) (n.factorization p)

/-- 把 `Ωφ` 摊到任一含其支撑的 Finset 上(多余素轴处 `S(0)=0`)。 -/
private theorem goldWeight_eq_sum_of_subset {n : ℕ} {s : Finset ℕ}
    (hsub : n.factorization.support ⊆ s) :
    goldWeight n = ∑ p ∈ s, S (n.factorization p) := by
  refine Finset.sum_subset hsub ?_
  intro p _ hp
  rw [Finsupp.notMem_support_iff.mp hp, S_at0]

/-- **oracle-suggested 定理(金权重拟同态)**:`Ωφ(mn) = Ωφ m + Ωφ n − κφ(m,n)`。 -/
theorem goldWeight_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    goldWeight (m * n) = goldWeight m + goldWeight n - goldObstruction m n := by
  have hfac : (m * n).factorization = m.factorization + n.factorization :=
    Nat.factorization_mul hm hn
  set s := m.factorization.support ∪ n.factorization.support with hs
  have hSm := goldWeight_eq_sum_of_subset (n := m) (s := s) Finset.subset_union_left
  have hSn := goldWeight_eq_sum_of_subset (n := n) (s := s) Finset.subset_union_right
  have hSmn : goldWeight (m * n) = ∑ p ∈ s, S (m.factorization p + n.factorization p) := by
    have hsub : (m * n).factorization.support ⊆ s := by
      rw [hfac]; exact Finsupp.support_add
    rw [goldWeight_eq_sum_of_subset hsub]
    apply Finset.sum_congr rfl
    intro p _
    rw [hfac, Finsupp.add_apply]
  rw [hSmn, hSm, hSn, goldObstruction, ← hs, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  unfold cDef
  ring

/-- **oracle-suggested 推论(互素严格可加)**:`m, n` 互素时 `Ωφ(mn) = Ωφ m + Ωφ n`。 -/
theorem goldWeight_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : Nat.Coprime m n) :
    goldWeight (m * n) = goldWeight m + goldWeight n := by
  rw [goldWeight_mul hm hn]
  have hdisj : Disjoint m.factorization.support n.factorization.support := by
    simp only [Nat.support_factorization]
    exact Nat.Coprime.disjoint_primeFactors hcop
  have hκ : goldObstruction m n = 0 := by
    rw [goldObstruction, Finset.sum_union hdisj]
    have h1 : ∑ p ∈ m.factorization.support,
        cDef (m.factorization p) (n.factorization p) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hpn : n.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff]; exact Finset.disjoint_left.mp hdisj hp
      rw [hpn]; unfold cDef; simp [S_at0]
    have h2 : ∑ p ∈ n.factorization.support,
        cDef (m.factorization p) (n.factorization p) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have hpm : m.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff]; exact Finset.disjoint_right.mp hdisj hp
      rw [hpm]; unfold cDef; simp [S_at0]
    rw [h1, h2]; ring
  rw [hκ]; ring

end UnifiedTheory
