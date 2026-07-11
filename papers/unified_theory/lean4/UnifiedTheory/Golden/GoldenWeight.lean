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

/-- 把 `Ωφ` 摊到任一含其支撑的 Finset 上(多余素轴处 `S(0)=0`)。可复用基建。 -/
theorem goldWeight_eq_sum_of_subset {n : ℕ} {s : Finset ℕ}
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

/-- 位移读数 `S` 单调:`a ≤ b ⟹ S a ≤ S b`(`(a+1)φ` 随 `a` 增,floor 保序)。 -/
theorem S_mono : Monotone S := by
  intro a b hab
  have hφ : (0 : ℝ) < Real.goldenRatio := by linarith [Real.one_lt_goldenRatio]
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hmul : ((a : ℝ) + 1) * Real.goldenRatio ≤ ((b : ℝ) + 1) * Real.goldenRatio :=
    mul_le_mul_of_nonneg_right (by linarith) hφ.le
  have hfl := Int.floor_le_floor hmul
  unfold S
  omega

/-- `S` 非负(`S 0 = 0` 且单调)。 -/
theorem S_nonneg (v : ℕ) : 0 ≤ S v := by
  have := S_mono (Nat.zero_le v)
  rwa [S_at0] at this

/-- 金权重非负。 -/
theorem goldWeight_nonneg (n : ℕ) : 0 ≤ goldWeight n :=
  Finset.sum_nonneg (fun _ _ => S_nonneg _)

/-- **金权重是整除格上的单调秩**:`m ∣ n`(`n ≠ 0`)时 `Ωφ m ≤ Ωφ n`。
与 `Gvec_dvd_iff`(整除 ↔ 逐坐标 ≤)对齐——金权重保序整除格到 `(ℤ, ≤)`。 -/
theorem goldWeight_mono_of_dvd {m n : ℕ} (hn : n ≠ 0) (hdvd : m ∣ n) :
    goldWeight m ≤ goldWeight n := by
  have hm : m ≠ 0 := fun h => hn (by rw [h] at hdvd; exact Nat.eq_zero_of_zero_dvd hdvd)
  have hle : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).mpr hdvd
  have hsub : m.factorization.support ⊆ n.factorization.support := by
    simp only [Nat.support_factorization]
    exact Nat.primeFactors_mono hdvd hn
  rw [goldWeight_eq_sum_of_subset (n := m) (s := n.factorization.support) hsub]
  unfold goldWeight
  exact Finset.sum_le_sum (fun p _ => S_mono (Finsupp.le_def.mp hle p))

/-- `S` 严格单调:`φ > 1` 令 `(a+1)φ` 每步至少前进一个整数,故 floor 严格增。 -/
theorem S_strictMono : StrictMono S := by
  intro a b hab
  have hφ1 : (1 : ℝ) < Real.goldenRatio := Real.one_lt_goldenRatio
  have hb : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have step : ((a : ℝ) + 1) * Real.goldenRatio + 1 ≤ ((b : ℝ) + 1) * Real.goldenRatio := by
    have hmul : ((a : ℝ) + 2) * Real.goldenRatio ≤ ((b : ℝ) + 1) * Real.goldenRatio :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith [hmul, hφ1]
  have hfl : ⌊((a : ℝ) + 1) * Real.goldenRatio⌋ + 1
      ≤ ⌊((b : ℝ) + 1) * Real.goldenRatio⌋ := by
    have := Int.floor_le_floor step
    rwa [Int.floor_add_one] at this
  unfold S
  omega

/-- **金权重是整除格上的严格秩**:`m ∣ n`、`m ≠ n`(`n ≠ 0`)时 `Ωφ m < Ωφ n`。
真因子严格降低金权重——金权重是整除严格序到 `(ℤ, <)` 的序嵌入。 -/
theorem goldWeight_strictMono_of_dvd {m n : ℕ} (hn : n ≠ 0) (hdvd : m ∣ n) (hne : m ≠ n) :
    goldWeight m < goldWeight n := by
  have hm : m ≠ 0 := fun h => hn (by rw [h] at hdvd; exact Nat.eq_zero_of_zero_dvd hdvd)
  have hle : m.factorization ≤ n.factorization :=
    (Nat.factorization_le_iff_dvd hm hn).mpr hdvd
  have hsub : m.factorization.support ⊆ n.factorization.support := by
    simp only [Nat.support_factorization]
    exact Nat.primeFactors_mono hdvd hn
  have hne_fact : m.factorization ≠ n.factorization :=
    fun h => hne (Nat.eq_of_factorization_eq hm hn (fun p => by rw [h]))
  obtain ⟨p, hp⟩ : ∃ p, m.factorization p ≠ n.factorization p := by
    by_contra hcon
    push_neg at hcon
    exact hne_fact (Finsupp.ext hcon)
  have hplt : m.factorization p < n.factorization p :=
    lt_of_le_of_ne (Finsupp.le_def.mp hle p) hp
  have hpmem : p ∈ n.factorization.support := by
    rw [Finsupp.mem_support_iff]; omega
  rw [goldWeight_eq_sum_of_subset (n := m) (s := n.factorization.support) hsub]
  unfold goldWeight
  exact Finset.sum_lt_sum (fun i _ => S_mono (Finsupp.le_def.mp hle i))
    ⟨p, hpmem, S_strictMono hplt⟩

/-- 障碍只落在公共素轴上:非公共轴处某个指数为 `0`,`cDef` 归零。 -/
theorem goldObstruction_eq_sum_inter (m n : ℕ) :
    goldObstruction m n
      = ∑ p ∈ m.factorization.support ∩ n.factorization.support,
          cDef (m.factorization p) (n.factorization p) := by
  unfold goldObstruction
  refine (Finset.sum_subset (Finset.inter_subset_left.trans Finset.subset_union_left) ?_).symm
  intro p _ hpI
  rw [Finset.mem_inter] at hpI
  by_cases hpm : p ∈ m.factorization.support
  · have hpn : p ∉ n.factorization.support := fun h => hpI ⟨hpm, h⟩
    rw [Finsupp.notMem_support_iff.mp hpn]; unfold cDef; simp [S_at0]
  · rw [Finsupp.notMem_support_iff.mp hpm]; unfold cDef; simp [S_at0]

/-- **金权重是拟态射(defect 受公共素轴数界定)**:`Ωφ` 偏离可加的量
`|Ωφ(mn) − Ωφ m − Ωφ n|` 至多为 `m, n` 的公共素轴个数——由亏空三值律 `cDef ∈ {−1,0,1}` 压出。
互素时公共轴为空,defect 归零(见 `goldWeight_mul_of_coprime`)。 -/
theorem goldWeight_defect_bound {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    |goldWeight (m * n) - goldWeight m - goldWeight n|
      ≤ ((m.factorization.support ∩ n.factorization.support).card : ℤ) := by
  have hcd : ∀ a b : ℕ, |cDef a b| ≤ (1 : ℤ) := by
    intro a b; rcases cDef_mem a b with h | h | h <;> rw [h] <;> norm_num
  rw [goldWeight_mul hm hn]
  have hrw : goldWeight m + goldWeight n - goldObstruction m n - goldWeight m - goldWeight n
      = - goldObstruction m n := by ring
  rw [hrw, abs_neg, goldObstruction_eq_sum_inter]
  calc |∑ p ∈ m.factorization.support ∩ n.factorization.support,
          cDef (m.factorization p) (n.factorization p)|
      ≤ ∑ p ∈ m.factorization.support ∩ n.factorization.support,
          |cDef (m.factorization p) (n.factorization p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ m.factorization.support ∩ n.factorization.support, (1 : ℤ) :=
        Finset.sum_le_sum (fun p _ => hcd _ _)
    _ = ((m.factorization.support ∩ n.factorization.support).card : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end UnifiedTheory
