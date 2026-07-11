import UnifiedTheory.Zeta.WeilExplicit
import Mathlib

namespace UnifiedTheory

open scoped Real

/-- **标准加权 zeta 素边**:带 `p^{-(m)/2}` 权(此处 `m=k+1≥1`)的显式公式素边,与阿基米德项配对。 -/
noncomputable def primeSideZeta (g : ℝ → ℝ) : ℝ :=
  ∑' (p : Nat.Primes) (k : ℕ),
    Real.log (p : ℝ) * ((p : ℝ) ^ (-((k : ℝ) + 1) / 2))
      * (g (((k : ℝ) + 1) * Real.log (p : ℝ))
          + g (-(((k : ℝ) + 1) * Real.log (p : ℝ))))

/-- **加权素边小支撑消没**:支集 ⊂ `(−log2, log2)` 时,加权素边也为 0(逐项消没,权因子乘零)。 -/
theorem primeSideZeta_eq_zero_of_smallSupport (g : ℝ → ℝ)
    (hg : ∀ x, g x ≠ 0 → x ∈ Set.Ioo (-(Real.log 2)) (Real.log 2)) :
    primeSideZeta g = 0 := by
  calc
    primeSideZeta g = ∑' (_p : Nat.Primes), (0 : ℝ) := by
      unfold primeSideZeta
      apply tsum_congr
      intro p
      calc
        (∑' (k : ℕ),
            Real.log (p : ℝ) * ((p : ℝ) ^ (-((k : ℝ) + 1) / 2))
              * (g (((k : ℝ) + 1) * Real.log (p : ℝ))
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
          change
            Real.log (p : ℝ) * ((p : ℝ) ^ (-((k : ℝ) + 1) / 2))
              * (g x + g (-x)) = 0
          rw [hgx, hgnx]
          ring
        _ = 0 := tsum_zero
    _ = 0 := tsum_zero

end UnifiedTheory
