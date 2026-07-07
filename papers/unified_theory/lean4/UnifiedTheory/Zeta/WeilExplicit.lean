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

end

end UnifiedTheory
