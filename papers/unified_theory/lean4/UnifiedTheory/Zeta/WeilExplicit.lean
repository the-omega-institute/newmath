import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace UnifiedTheory

open Real

noncomputable section

/-- 素数幂显式项之和(Weil 显式公式的**素边**):对每个素数 `p` 与 `k`,项为
`log p · (g((k+1)·log p) + g(−(k+1)·log p))`。`k+1` 保证幂次 ≥ 1。 -/
noncomputable def primeSide (g : ℝ → ℝ) : ℝ :=
  ∑' (p : Nat.Primes) (k : ℕ),
    Real.log (p : ℝ) * (g (((k : ℝ) + 1) * Real.log (p : ℝ))
      + g (-(((k : ℝ) + 1) * Real.log (p : ℝ))))

/-- **素边消没引理(无条件)**:若 `g` 的支集落在开窗 `(−log 2, log 2)` 内,则素边为 0。
每个素数幂对数 `(k+1)·log p ≥ log 2` 落在开窗外,故逐项为零。 -/
theorem primeSide_eq_zero_of_smallSupport (g : ℝ → ℝ)
    (hg : ∀ x, g x ≠ 0 → x ∈ Set.Ioo (-(Real.log 2)) (Real.log 2)) :
    primeSide g = 0 := by
  calc
    primeSide g = ∑' (_p : Nat.Primes), (0 : ℝ) := by
      unfold primeSide
      apply tsum_congr
      intro p
      calc
        (∑' (k : ℕ),
            Real.log (p : ℝ) * (g (((k : ℝ) + 1) * Real.log (p : ℝ))
              + g (-(((k : ℝ) + 1) * Real.log (p : ℝ))))) =
            ∑' (_k : ℕ), (0 : ℝ) := by
          apply tsum_congr
          intro k
          let x : ℝ := ((k : ℝ) + 1) * Real.log (p : ℝ)
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast p.2.two_le
          have hlog2p : Real.log 2 ≤ Real.log (p : ℝ) :=
            Real.log_le_log (by norm_num) hp2
          have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) :=
            Real.log_nonneg (by linarith)
          have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
            have hk0 : (0 : ℝ) ≤ (k : ℝ) := by
              exact_mod_cast Nat.zero_le k
            linarith
          have hlogp_le_x : Real.log (p : ℝ) ≤ x := by
            dsimp [x]
            exact le_mul_of_one_le_left hlogp_nonneg hk1
          have hxge : Real.log 2 ≤ x := by
            linarith
          have hgx : g x = 0 := by
            by_contra hneq
            have hmem := hg x hneq
            have hlt : x < Real.log 2 := (Set.mem_Ioo.mp hmem).2
            linarith
          have hgnx : g (-x) = 0 := by
            by_contra hneq
            have hmem := hg (-x) hneq
            have hlt : x < Real.log 2 := by
              have hleft : -(Real.log 2) < -x := (Set.mem_Ioo.mp hmem).1
              linarith
            linarith
          change Real.log (p : ℝ) * (g x + g (-x)) = 0
          rw [hgx, hgnx]
          ring
        _ = 0 := tsum_zero
    _ = 0 := tsum_zero

private lemma primeSide_witness_pos_eq_iff (p : Nat.Primes) (k : ℕ) :
    ((k : ℝ) + 1) * Real.log (p : ℝ) = Real.log 2 ↔ (p : ℕ) = 2 ∧ k = 0 := by
  constructor
  · intro hx
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast p.2.two_le
    have hlog2p : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) hp2
    have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) := by
      linarith
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast Nat.zero_le k
      linarith
    have hlogp_le_x :
        Real.log (p : ℝ) ≤ ((k : ℝ) + 1) * Real.log (p : ℝ) :=
      le_mul_of_one_le_left hlogp_nonneg hk1
    have hlogp_le_log2 : Real.log (p : ℝ) ≤ Real.log 2 := by
      simpa [hx] using hlogp_le_x
    have hlogp_eq : Real.log (p : ℝ) = Real.log 2 :=
      le_antisymm hlogp_le_log2 hlog2p
    have hp_pos : 0 < (p : ℝ) := by
      exact_mod_cast p.2.pos
    have hp_real : (p : ℝ) = 2 := by
      have h_exp := congrArg Real.exp hlogp_eq
      rwa [Real.exp_log hp_pos, Real.exp_log (by norm_num)] at h_exp
    have hp_nat : (p : ℕ) = 2 := by
      exact_mod_cast hp_real
    have hx_log2 : ((k : ℝ) + 1) * Real.log 2 = Real.log 2 := by
      simpa [hlogp_eq] using hx
    have hk1_eq : (k : ℝ) + 1 = 1 := by
      have hmul : ((k : ℝ) + 1) * Real.log 2 = 1 * Real.log 2 := by
        simpa using hx_log2
      exact mul_right_cancel₀ (ne_of_gt hlog2pos) hmul
    have hk_real : (k : ℝ) = 0 := by
      linarith
    have hk_nat : k = 0 := by
      exact_mod_cast hk_real
    exact ⟨hp_nat, hk_nat⟩
  · rintro ⟨hp, hk⟩
    subst hk
    have hp_real : (p : ℝ) = 2 := by
      exact_mod_cast hp
    simp [hp_real]

private lemma primeSide_witness_neg_ne (p : Nat.Primes) (k : ℕ) :
    -(((k : ℝ) + 1) * Real.log (p : ℝ)) ≠ Real.log 2 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast p.2.two_le
  have hlog2p : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) hp2
  have hlogp_nonneg : 0 ≤ Real.log (p : ℝ) := by
    linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.zero_le k
    linarith
  have hlogp_le_x :
      Real.log (p : ℝ) ≤ ((k : ℝ) + 1) * Real.log (p : ℝ) :=
    le_mul_of_one_le_left hlogp_nonneg hk1
  have hxge : Real.log 2 ≤ ((k : ℝ) + 1) * Real.log (p : ℝ) := by
    linarith
  intro h
  linarith

private lemma primeSide_witness_summand_eq (p : Nat.Primes) (k : ℕ) :
    Real.log (p : ℝ) *
        ((if ((k : ℝ) + 1) * Real.log (p : ℝ) = Real.log 2 then (1 : ℝ) else 0) +
          if -(((k : ℝ) + 1) * Real.log (p : ℝ)) = Real.log 2 then (1 : ℝ) else 0) =
      if (p : ℕ) = 2 ∧ k = 0 then Real.log 2 else 0 := by
  have hposiff := primeSide_witness_pos_eq_iff p k
  have hneg := primeSide_witness_neg_ne p k
  by_cases hpk : (p : ℕ) = 2 ∧ k = 0
  · have hpos : ((k : ℝ) + 1) * Real.log (p : ℝ) = Real.log 2 := hposiff.mpr hpk
    have hp_real : (p : ℝ) = 2 := by
      exact_mod_cast hpk.1
    rw [if_pos hpk, if_pos hpos, if_neg hneg, hp_real]
    ring
  · have hpos : ((k : ℝ) + 1) * Real.log (p : ℝ) ≠ Real.log 2 := by
      intro hx
      exact hpk (hposiff.mp hx)
    rw [if_neg hpk, if_neg hpos, if_neg hneg]
    ring

/-- **素边非虚(校准见证)**:单点见证 `g = 𝟙_{log 2}` 恰好挑出 `p=2, k=0` 项,
`primeSide g = log 2 ≠ 0`。说明小支集消没引理非虚——素边确实探测素数幂对数,
且 `log 2` 是精确边界。 -/
theorem primeSide_witness :
    primeSide (fun y => if y = Real.log 2 then (1 : ℝ) else 0) = Real.log 2 := by
  let q : Nat.Primes := ⟨2, Nat.prime_two⟩
  unfold primeSide
  calc
    (∑' (p : Nat.Primes) (k : ℕ),
        Real.log (p : ℝ) *
          ((if ((k : ℝ) + 1) * Real.log (p : ℝ) = Real.log 2 then (1 : ℝ) else 0) +
            if -(((k : ℝ) + 1) * Real.log (p : ℝ)) = Real.log 2 then (1 : ℝ) else 0)) =
        ∑' (p : Nat.Primes) (k : ℕ), if (p : ℕ) = 2 ∧ k = 0 then Real.log 2 else 0 := by
      apply tsum_congr
      intro p
      apply tsum_congr
      intro k
      exact primeSide_witness_summand_eq p k
    _ = ∑' (p : Nat.Primes), if (p : ℕ) = 2 then Real.log 2 else 0 := by
      apply tsum_congr
      intro p
      by_cases hp : (p : ℕ) = 2
      · calc
          (∑' (k : ℕ), if (p : ℕ) = 2 ∧ k = 0 then Real.log 2 else 0) =
              (if (p : ℕ) = 2 ∧ (0 : ℕ) = 0 then Real.log 2 else 0) := by
            apply tsum_eq_single 0
            intro k hk
            rw [if_neg]
            intro h
            exact hk h.2
          _ = if (p : ℕ) = 2 then Real.log 2 else 0 := by
            simp [hp]
      · calc
          (∑' (k : ℕ), if (p : ℕ) = 2 ∧ k = 0 then Real.log 2 else 0) =
              ∑' (_k : ℕ), (0 : ℝ) := by
            apply tsum_congr
            intro k
            rw [if_neg]
            intro h
            exact hp h.1
          _ = if (p : ℕ) = 2 then Real.log 2 else 0 := by
            rw [tsum_zero]
            simp [hp]
    _ = (if (q : ℕ) = 2 then Real.log 2 else 0) := by
      apply tsum_eq_single q
      intro p hp
      rw [if_neg]
      intro hp2
      apply hp
      apply Subtype.ext
      simpa [q] using hp2
    _ = Real.log 2 := by
      simp [q]

/-- 素边非平凡:存在测试函数使素边非零(小支集假设做实事)。 -/
theorem primeSide_not_identically_zero :
    ∃ g : ℝ → ℝ, primeSide g ≠ 0 := by
  refine ⟨fun y => if y = Real.log 2 then (1 : ℝ) else 0, ?_⟩
  rw [primeSide_witness]
  exact ne_of_gt (Real.log_pos (by norm_num))

/-- 抽象 Weil 显式公式泛函:阿基米德项(抽象载体)+ 素边(显式)。 -/
structure WeilFunctional where
  archimedean : (ℝ → ℝ) → ℝ

/-- 泛函求值。 -/
def WeilFunctional.eval (W : WeilFunctional) (g : ℝ → ℝ) : ℝ :=
  W.archimedean g + primeSide g

/-- **小支集约化(无条件)**:支集在 `(−log 2, log 2)` 内时,Weil 泛函 = 阿基米德项。 -/
theorem WeilFunctional.eval_smallSupport (W : WeilFunctional) (g : ℝ → ℝ)
    (hg : ∀ x, g x ≠ 0 → x ∈ Set.Ioo (-(Real.log 2)) (Real.log 2)) :
    W.eval g = W.archimedean g := by
  rw [WeilFunctional.eval, primeSide_eq_zero_of_smallSupport g hg, add_zero]

/-- **小支集条件正性**:小支集 + 阿基米德正性假设(开叶子)⇒ Weil 泛函 ≥ 0。
`harch` 是**开叶子假设**(Connes–Consani 阿基米德正性,本文件不证),不是本文件的结论。 -/
theorem WeilFunctional.eval_nonneg_of_smallSupport (W : WeilFunctional) (g : ℝ → ℝ)
    (hg : ∀ x, g x ≠ 0 → x ∈ Set.Ioo (-(Real.log 2)) (Real.log 2))
    (harch : 0 ≤ W.archimedean g) :
    0 ≤ W.eval g := by
  rw [WeilFunctional.eval_smallSupport W g hg]
  exact harch

/-- **Weil log-3 腔:素边单项约化(第一有限包实例)**。支集在 `(−log3, log3)` 内时,唯一
`< 3` 的素数幂是 `2`,故素边恰为单一 `p=2, m=1` 项 `log 2·(g(log2)+g(−log2))`。 -/
theorem primeSide_eq_single_of_support_log3 (g : ℝ → ℝ)
    (hg : ∀ x, g x ≠ 0 → x ∈ Set.Ioo (-(Real.log 3)) (Real.log 3)) :
    primeSide g = Real.log 2 * (g (Real.log 2) + g (-(Real.log 2))) := by
  let q : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hsummand : ∀ (p : Nat.Primes) (k : ℕ),
      Real.log (p : ℝ) * (g (((k : ℝ) + 1) * Real.log (p : ℝ))
          + g (-(((k : ℝ) + 1) * Real.log (p : ℝ))))
        = if (p : ℕ) = 2 ∧ k = 0
            then Real.log 2 * (g (Real.log 2) + g (-(Real.log 2))) else 0 := by
    intro p k
    by_cases hpk : (p : ℕ) = 2 ∧ k = 0
    · obtain ⟨hp2, hk0⟩ := hpk
      have hpR : (p : ℝ) = 2 := by exact_mod_cast hp2
      subst hk0
      rw [if_pos ⟨hp2, rfl⟩, hpR]
      norm_num
    · rw [if_neg hpk]
      have h3le : 3 ≤ (p : ℕ) ^ (k + 1) := by
        by_cases hp3 : 3 ≤ (p : ℕ)
        · calc (3 : ℕ) ≤ (p : ℕ) := hp3
            _ = (p : ℕ) ^ 1 := (pow_one _).symm
            _ ≤ (p : ℕ) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        · have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
          have hpeq : (p : ℕ) = 2 := by omega
          have hk : k ≠ 0 := fun hk0 => hpk ⟨hpeq, hk0⟩
          calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
            _ ≤ (p : ℕ) ^ (k + 1) := by
                rw [hpeq]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3leR : (3 : ℝ) ≤ (p : ℝ) ^ (k + 1) := by exact_mod_cast h3le
      have hxeq : ((k : ℝ) + 1) * Real.log (p : ℝ) = Real.log ((p : ℝ) ^ (k + 1)) := by
        rw [Real.log_pow]; push_cast; ring
      have hxge : Real.log 3 ≤ ((k : ℝ) + 1) * Real.log (p : ℝ) := by
        rw [hxeq]; exact Real.log_le_log (by norm_num) h3leR
      set x := ((k : ℝ) + 1) * Real.log (p : ℝ) with hx
      have hgx : g x = 0 := by
        by_contra h
        have hmem := hg x h
        rw [Set.mem_Ioo] at hmem
        linarith [hmem.2]
      have hgnx : g (-x) = 0 := by
        by_contra h
        have hmem := hg (-x) h
        rw [Set.mem_Ioo] at hmem
        linarith [hmem.1]
      rw [hgx, hgnx]; ring
  calc primeSide g
      = ∑' (p : Nat.Primes) (k : ℕ),
          (if (p : ℕ) = 2 ∧ k = 0
            then Real.log 2 * (g (Real.log 2) + g (-(Real.log 2))) else 0) := by
        unfold primeSide
        exact tsum_congr (fun p => tsum_congr (fun k => hsummand p k))
    _ = ∑' (p : Nat.Primes),
          (if (p : ℕ) = 2
            then Real.log 2 * (g (Real.log 2) + g (-(Real.log 2))) else 0) := by
        apply tsum_congr
        intro p
        by_cases hp : (p : ℕ) = 2
        · rw [tsum_eq_single 0 (fun k hk => by
              rw [if_neg]; rintro ⟨_, hk0⟩; exact hk hk0)]
          rw [if_pos ⟨hp, rfl⟩, if_pos hp]
        · have hz : ∀ k : ℕ,
              (if (p : ℕ) = 2 ∧ k = 0
                then Real.log 2 * (g (Real.log 2) + g (-(Real.log 2))) else 0) = 0 := by
            intro k; rw [if_neg]; rintro ⟨hp2, _⟩; exact hp hp2
          rw [if_neg hp, tsum_congr hz, tsum_zero]
    _ = (if (q : ℕ) = 2
            then Real.log 2 * (g (Real.log 2) + g (-(Real.log 2))) else 0) := by
        apply tsum_eq_single q
        intro p hp
        rw [if_neg]
        intro hp2
        apply hp
        apply Subtype.ext
        simpa [q] using hp2
    _ = Real.log 2 * (g (Real.log 2) + g (-(Real.log 2))) := by
        simp [q]

/-- **Weil 泛函在 log-3 腔 = 阿基米德项 + 单一素数移位**(有限包证书形状)。 -/
theorem WeilFunctional.eval_log3_chamber (W : WeilFunctional) (g : ℝ → ℝ)
    (hg : ∀ x, g x ≠ 0 → x ∈ Set.Ioo (-(Real.log 3)) (Real.log 3)) :
    W.eval g = W.archimedean g + Real.log 2 * (g (Real.log 2) + g (-(Real.log 2))) := by
  rw [WeilFunctional.eval, primeSide_eq_single_of_support_log3 g hg]

end

end UnifiedTheory
