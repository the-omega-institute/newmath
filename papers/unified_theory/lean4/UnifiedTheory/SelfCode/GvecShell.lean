import UnifiedTheory.SelfCode.GvecWeight
import UnifiedTheory.Golden.GoldenWeightSquarefree
import Mathlib

namespace UnifiedTheory.SelfCode

open scoped BigOperators
open UnifiedTheory

private theorem sum_nonneg_eq_one_iff_single_one {k : ℕ} (E : ℕ → ℤ) (x : Fin k → ℕ)
    (hEnonneg : ∀ n, 0 ≤ E n)
    (hE0_iff : ∀ n, E n = 0 ↔ n = 0)
    (hE1_iff : ∀ n, E n = 1 ↔ n = 1) :
    (∑ i : Fin k, E (x i)) = 1 ↔
      ∃ i : Fin k, x i = 1 ∧ ∀ j : Fin k, j ≠ i → x j = 0 := by
  constructor
  · intro hsum
    obtain ⟨i0, hi0_ne⟩ : ∃ i : Fin k, E (x i) ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      have hzero : (∑ i : Fin k, E (x i)) = 0 := by
        exact Finset.sum_eq_zero (fun i _ => hnone i)
      omega
    have hsplit :
        E (x i0) + ∑ j ∈ (Finset.univ.erase i0), E (x j)
          = ∑ j : Fin k, E (x j) :=
      Finset.add_sum_erase (s := Finset.univ) (a := i0) (f := fun j => E (x j))
        (Finset.mem_univ i0)
    have hsplit_one :
        E (x i0) + ∑ j ∈ (Finset.univ.erase i0), E (x j) = 1 := by
      rw [hsplit, hsum]
    have hi0_pos : 1 ≤ E (x i0) := by
      have hi0_nonneg : 0 ≤ E (x i0) := hEnonneg (x i0)
      omega
    have herase_nonneg : 0 ≤ ∑ j ∈ (Finset.univ.erase i0), E (x j) :=
      Finset.sum_nonneg (fun j _ => hEnonneg (x j))
    have hi0_E : E (x i0) = 1 := by
      omega
    have herase_sum_zero : ∑ j ∈ (Finset.univ.erase i0), E (x j) = 0 := by
      omega
    have herase_zero :
        ∀ j ∈ (Finset.univ.erase i0), E (x j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hEnonneg (x j))).mp
        herase_sum_zero
    refine ⟨i0, (hE1_iff (x i0)).mp hi0_E, ?_⟩
    intro j hj_ne
    have hj_mem : j ∈ (Finset.univ.erase i0) := by
      simp [Finset.mem_erase, hj_ne]
    exact (hE0_iff (x j)).mp (herase_zero j hj_mem)
  · rintro ⟨i0, hi0, hrest⟩
    have hsplit :
        E (x i0) + ∑ j ∈ (Finset.univ.erase i0), E (x j)
          = ∑ j : Fin k, E (x j) :=
      Finset.add_sum_erase (s := Finset.univ) (a := i0) (f := fun j => E (x j))
        (Finset.mem_univ i0)
    have hi0_E : E (x i0) = 1 := (hE1_iff (x i0)).mpr hi0
    have herase_sum_zero : ∑ j ∈ (Finset.univ.erase i0), E (x j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj_ne : j ≠ i0 := (Finset.mem_erase.mp hj).1
      exact (hE0_iff (x j)).mpr (hrest j hj_ne)
    linarith [hsplit, hi0_E, herase_sum_zero]

/-- **Gvec 第一金壳 = 坐标单位向量**:`Ωφ(Gvec x) = 2k+1 ↔ 恰有一个坐标 =1 其余 =0`。 -/
theorem gvec_Omega_first_shell {k : ℕ} (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (x : Fin k → ℕ) :
    goldWeight (Gvec p x) = 2 * k + 1 ↔
      ∃ i : Fin k, x i = 1 ∧ ∀ j : Fin k, j ≠ i → x j = 0 := by
  let E : ℕ → ℤ := fun n => S (n + 1) - 2
  have hE0 : E 0 = 0 := by
    dsimp [E]
    norm_num [S_at1]
  have hE1 : E 1 = 1 := by
    dsimp [E]
    norm_num [S_at2]
  have hEnonneg : ∀ n, 0 ≤ E n := by
    intro n
    dsimp [E]
    have hS : (2 : ℤ) ≤ S (n + 1) := by
      calc
        (2 : ℤ) = S 1 := S_at1.symm
        _ ≤ S (n + 1) := S_mono (by omega)
    omega
  have hE0_iff : ∀ n, E n = 0 ↔ n = 0 := by
    intro n
    constructor
    · intro h
      have hS : S (n + 1) = S 1 := by
        dsimp [E] at h
        rw [S_at1]
        omega
      have hn : n + 1 = 1 := S_strictMono.injective hS
      omega
    · intro hn
      subst hn
      exact hE0
  have hE1_iff : ∀ n, E n = 1 ↔ n = 1 := by
    intro n
    constructor
    · intro h
      have hS : S (n + 1) = S 2 := by
        dsimp [E] at h
        rw [S_at2]
        omega
      have hn : n + 1 = 2 := S_strictMono.injective hS
      omega
    · intro hn
      subst hn
      exact hE1
  have hsum_expand :
      (∑ i : Fin k, S (x i + 1)) = (∑ i : Fin k, E (x i)) + 2 * k := by
    calc
      (∑ i : Fin k, S (x i + 1))
          = ∑ i : Fin k, (E (x i) + 2) := by
            apply Finset.sum_congr rfl
            intro i _
            dsimp [E]
            omega
      _ = (∑ i : Fin k, E (x i)) + ∑ _i : Fin k, (2 : ℤ) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ i : Fin k, E (x i)) + 2 * k := by
            simp [Fintype.card_fin, nsmul_eq_mul]
            ring
  have hgold_iff_sumE :
      goldWeight (Gvec p x) = 2 * k + 1 ↔ (∑ i : Fin k, E (x i)) = 1 := by
    rw [goldWeight_Gvec p hp hinj x, hsum_expand]
    constructor <;> intro h <;> omega
  rw [hgold_iff_sumE]
  exact sum_nonneg_eq_one_iff_single_one E x hEnonneg hE0_iff hE1_iff

end UnifiedTheory.SelfCode
