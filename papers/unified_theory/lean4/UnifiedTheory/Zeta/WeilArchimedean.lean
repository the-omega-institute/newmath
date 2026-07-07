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

open Filter Topology in
/-- **阿基米德核在 0 处可去奇异**:`g` 在 0 可微时,`archKernel g t → g 0 / 2`(t→0⁺)。 -/
theorem tendsto_archKernel_zero {g : ℝ → ℝ} (hg : DifferentiableAt ℝ g 0) :
    Filter.Tendsto (archKernel g) (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (g 0 / 2)) := by
  let N : ℝ → ℝ := fun t => Real.exp (t / 2) * (g t + g (-t)) - 2 * g 0
  let D : ℝ → ℝ := fun t => Real.exp t - Real.exp (-t)
  have hgd : HasDerivAt g (deriv g 0) 0 := hg.hasDerivAt
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) 0 := by
    simpa using hasDerivAt_neg (0 : ℝ)
  have hgn : HasDerivAt (fun t : ℝ => g (-t)) (-(deriv g 0)) 0 := by
    have hgdNeg : HasDerivAt g (deriv g 0) (-0) := by
      simpa using hgd
    simpa [Function.comp_def] using hgdNeg.comp 0 hneg
  have hsum : HasDerivAt (fun t : ℝ => g t + g (-t)) 0 0 := by
    simpa using hgd.add hgn
  have hhalf : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).div_const (2 : ℝ)
  have hexp2 : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (1 / 2) 0 := by
    simpa using hhalf.exp
  have hprod :
      HasDerivAt (fun t : ℝ => Real.exp (t / 2) * (g t + g (-t))) (g 0) 0 := by
    have h := hexp2.mul hsum
    convert h using 1
    ring_nf
  have hN : HasDerivAt N (g 0) 0 := by
    simpa [N] using hprod.sub_const (2 * g 0)
  have hD : HasDerivAt D 2 0 := by
    have hexp : HasDerivAt (fun t : ℝ => Real.exp t) 1 0 := by
      simpa using Real.hasDerivAt_exp (0 : ℝ)
    have hexpNeg : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
      have hexpAtNegZero : HasDerivAt Real.exp (Real.exp (-0)) (-0) :=
        Real.hasDerivAt_exp (-0)
      simpa [Function.comp_def] using hexpAtNegZero.comp 0 hneg
    have h := hexp.sub hexpNeg
    convert h using 1
    norm_num
  have hN0 : N 0 = 0 := by
    simp [N]
    ring
  have hD0 : D 0 = 0 := by
    simp [D]
  have hslopeN :
      Tendsto (fun t : ℝ => t⁻¹ * N t) (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) := by
    have h := hN.tendsto_slope_zero_right
    simpa [hN0, zero_add] using h
  have hslopeD :
      Tendsto (fun t : ℝ => t⁻¹ * D t) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := by
    have h := hD.tendsto_slope_zero_right
    simpa [hD0, zero_add] using h
  have hquot :
      Tendsto (fun t : ℝ => (t⁻¹ * N t) / (t⁻¹ * D t))
        (𝓝[>] (0 : ℝ)) (𝓝 (g 0 / 2)) := by
    exact hslopeN.div hslopeD (by norm_num)
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htne : t ≠ 0 := ne_of_gt ht
  have hkernel : archKernel g t = N t / D t := by
    simp [archKernel, N, D, htne]
  calc
    (t⁻¹ * N t) / (t⁻¹ * D t) = N t / D t := by
      field_simp [htne]
    _ = archKernel g t := hkernel.symm

/-- **Brick C(紧截断式)**:`archSmall g = −C∞·g0 − ∫_0^{log2} K_g − g0·archTail(log2)`。 -/
theorem archSmall_def (g : ℝ → ℝ) :
    archSmall g = - archConst * g 0
      - (∫ t in (0:ℝ)..Real.log 2, archKernel g t) - g 0 * archTail (Real.log 2) := by
  rfl

/-- 物理 Fourier 变换(约定 `∫ g(t) e^{iτt} dt`,非 2π 归一)。 -/
noncomputable def fourierPhys (g : ℝ → ℂ) (τ : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (Complex.I * (τ : ℂ) * (t : ℂ)) * g t

/-- Gamma 乘子 `Re ψ(1/4 + iτ/2) − log π`(`ψ = Complex.digamma`)。 -/
noncomputable def gammaMultiplier (τ : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℝ) + (τ / 2 : ℝ) * Complex.I)).re - Real.log Real.pi

/-- 阿基米德泛函之谱形(digamma 积分表示)。 -/
noncomputable def WInfSpectral (g : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) • ∫ τ : ℝ, (gammaMultiplier τ : ℂ) * fourierPhys g τ

/-- 自卷积平方 `(h ⋆ h̃)(x) = ∫ h(y) h(y − x) dy`(`h̃(x) := h(−x)`)。 -/
noncomputable def convSquare (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, h y * h (y - x)

/-- **开叶子:谱形 = 实积分形之等价**(卡 mathlib digamma Gauss 积分表示,TODO)。
本理论不证;登记为 O-6 邻域之精确命题。 -/
def ArchSpectralMatchesReal : Prop :=
  ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
    (∀ x, g x ≠ 0 → x ∈ Set.Ioo (-(Real.log 2)) (Real.log 2)) →
    WInfSpectral (fun t => (g t : ℂ)) = (archSmall g : ℂ)

/-- **开叶子(O-6):阿基米德正性(小支撑卷积平方类)** = Connes–Consani 小支撑
archimedean 正性;月级解析核心,本理论不证——登记为精确开命题。**不蕴含 RH**
(素边正性之 ∀-极限才是 RH 墙)。 -/
def ArchimedeanPositivity : Prop :=
  ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h →
    (∀ x, convSquare h x ≠ 0 → x ∈ Set.Ioo (-(Real.log 2)) (Real.log 2)) →
    0 ≤ archSmall (convSquare h)

open Filter Topology in
/-- **阿基米德核于 `[0, log2]` 连续**(`g` 连续且在 0 可微):去奇异 + 分母非零。 -/
theorem archKernel_continuousOn {g : ℝ → ℝ} (hgc : Continuous g)
    (hg0 : DifferentiableAt ℝ g 0) :
    ContinuousOn (archKernel g) (Set.Icc (0:ℝ) (Real.log 2)) := by
  intro x hx
  have hlog_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  by_cases hx0 : x = 0
  · subst x
    have hright : ContinuousWithinAt (archKernel g) (Set.Ioi (0 : ℝ)) 0 := by
      simpa [ContinuousWithinAt, archKernel] using tendsto_archKernel_zero (g := g) hg0
    have hici : ContinuousWithinAt (archKernel g) (Set.Ici (0 : ℝ)) 0 :=
      continuousWithinAt_Ioi_iff_Ici.mp hright
    exact (continuousWithinAt_Icc_iff_Ici hlog_pos).mpr hici
  · let q : ℝ → ℝ := fun t =>
      (Real.exp (t / 2) * (g t + g (-t)) - 2 * g 0) /
        (Real.exp t - Real.exp (-t))
    have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hden_ne : Real.exp x - Real.exp (-x) ≠ 0 := by
      have hlt : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.mpr (by linarith)
      linarith
    have hq_cont : ContinuousAt q x := by
      have hnum :
          ContinuousAt
            (fun t : ℝ => Real.exp (t / 2) * (g t + g (-t)) - 2 * g 0) x := by
        fun_prop
      have hden : ContinuousAt (fun t : ℝ => Real.exp t - Real.exp (-t)) x := by
        fun_prop
      exact hnum.div hden hden_ne
    have hne_eventually : ∀ᶠ t in 𝓝 x, t ≠ 0 := isOpen_ne.mem_nhds hx0
    have heq : archKernel g =ᶠ[𝓝[Set.Icc (0 : ℝ) (Real.log 2)] x] q := by
      filter_upwards [nhdsWithin_le_nhds hne_eventually] with t ht
      simp [archKernel, q, ht]
    exact hq_cont.continuousWithinAt.congr_of_eventuallyEq heq (by simp [archKernel, q, hx0])

/-- **阿基米德核于 `0..log2` 可积**(截断式 `WInfCompact` 之积分良定)。 -/
theorem archKernel_intervalIntegrable {g : ℝ → ℝ} (hgc : Continuous g)
    (hg0 : DifferentiableAt ℝ g 0) :
    IntervalIntegrable (archKernel g) MeasureTheory.volume 0 (Real.log 2) := by
  have hlog_nonneg : (0 : ℝ) ≤ Real.log 2 :=
    Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  exact ContinuousOn.intervalIntegrable_of_Icc hlog_nonneg
    (archKernel_continuousOn hgc hg0)

end UnifiedTheory
