import UnifiedTheory.Zeta.WeilExplicit
import Mathlib

namespace UnifiedTheory

open scoped Real
open MeasureTheory

/-- 阿基米德常数 `C∞ = γ + log(4π)`(Weil 显式公式阿基米德项常数)。 -/
noncomputable def archConst : ℝ := Real.eulerMascheroniConstant + Real.log (4 * Real.pi)

/-- 阿基米德核(去奇异化):`t=0` 处取可去极限 `g 0 / 2`。 -/
noncomputable def archKernel (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t = 0 then g 0 / 2
  else (Real.exp (t / 2) * (g t + g (-t)) - 2 * g 0) / (Real.exp t - Real.exp (-t))

/-- 阿基米德尾项系数 `log((e^A−1)/(e^A+1))`(把 `∫_A^∞` 闭合成有限式)。 -/
noncomputable def archTail (A : ℝ) : ℝ := Real.log ((Real.exp A - 1) / (Real.exp A + 1))

/-- 紧截断阿基米德泛函 `W∞^A(g) = −C∞·g0 − ∫_0^A K_g − g0·archTail A`。 -/
noncomputable def WInfCompact (A : ℝ) (g : ℝ → ℝ) : ℝ :=
  - archConst * g 0 - (∫ t in (0:ℝ)..A, archKernel g t) - g 0 * archTail A

/-- 小支撑阿基米德泛函(截断 `A = log 2`):支集 ⊂ `(−log2, log2)` 时的具体阿基米德项。 -/
noncomputable def archSmall (g : ℝ → ℝ) : ℝ := WInfCompact (Real.log 2) g

/-- 具体 Weil 泛函(小支撑标度):具体阿基米德项 + 显式素边。 -/
noncomputable def concreteW (g : ℝ → ℝ) : ℝ := archSmall g + primeSide g

/-- **小支撑约化(具体阿基米德版)**:支集 ⊂ `(−log2, log2)` 时,具体 Weil 泛函 = 具体阿基米德项
(素边逐项消没,已证)。**注:本定理不断言正性;正性是独立开叶子。** -/
theorem concreteW_eq_arch_of_smallSupport (g : ℝ → ℝ)
    (hg : ∀ x, g x ≠ 0 → x ∈ Set.Ioo (-(Real.log 2)) (Real.log 2)) :
    concreteW g = archSmall g := by
  rw [concreteW, primeSide_eq_zero_of_smallSupport g hg, add_zero]

end UnifiedTheory
