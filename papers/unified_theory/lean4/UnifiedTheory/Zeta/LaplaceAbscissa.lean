import Mathlib

namespace UnifiedTheory

open MeasureTheory Set

/-- **Laplace 数据**:实函数 `f`、下端 `u₀`、以及 `f` 于 `[u₀,∞)` 上的可测性。
这是 Landau 振荡定理引擎(源 F-7)横标基础设施的载体,以积分版镜像
mathlib 之 Dirichlet 级数 `LSeries.abscissaOfAbsConv`。 -/
structure LaplaceData where
  f : ℝ → ℝ
  u₀ : ℝ
  measf : AEStronglyMeasurable f (volume.restrict (Ici u₀))

/-- σ-横标收敛:实积分 `∫_{u≥u₀} f(u) e^{-σu}` 绝对可积。 -/
def LaplaceData.Converges (D : LaplaceData) (σ : ℝ) : Prop :=
  IntegrableOn (fun u => D.f u * Real.exp (-σ * u)) (Ici D.u₀)

/-- 复 Laplace 变换 `F(s) = ∫_{u≥u₀} f(u) e^{-su}`。 -/
noncomputable def LaplaceData.F (D : LaplaceData) (s : ℂ) : ℂ :=
  ∫ u in Ici D.u₀, (D.f u : ℂ) * Complex.exp (-s * u)

/-- **横标单调性**:σ 收敛且 `σ ≤ σ'` ⟹ σ' 收敛。于 `u ≥ u₀` 有
`|f e^{-σ'u}| ≤ e^{-(σ'-σ)u₀} |f e^{-σu}|`(因 `(σ'-σ)(u-u₀) ≥ 0`),
即被常数倍可积函数支配,故 σ' 之被积函数亦可积。这是横标良定义、
半平面收敛与后续解析延拓论证的基础。 -/
theorem LaplaceData.Converges.mono {D : LaplaceData} {σ σ' : ℝ}
    (hσ : D.Converges σ) (hle : σ ≤ σ') : D.Converges σ' := by
  set C : ℝ := Real.exp (-(σ' - σ) * D.u₀) with hCdef
  have hmeas' : AEStronglyMeasurable (fun u => D.f u * Real.exp (-σ' * u))
      (volume.restrict (Ici D.u₀)) :=
    D.measf.mul (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  refine (hσ.norm.const_mul C).mono' hmeas' ?_
  rw [ae_restrict_iff' measurableSet_Ici]
  filter_upwards with u hu
  have hu0 : D.u₀ ≤ u := hu
  have hexp : Real.exp (-σ' * u) ≤ C * Real.exp (-σ * u) := by
    rw [hCdef, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hle, sub_nonneg.mpr hu0]
  calc ‖D.f u * Real.exp (-σ' * u)‖
      = |D.f u| * Real.exp (-σ' * u) := by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    _ ≤ |D.f u| * (C * Real.exp (-σ * u)) :=
        mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
    _ = C * ‖D.f u * Real.exp (-σ * u)‖ := by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
        ring

/-- **绝对收敛横标** `σ_c ∈ EReal`:使 σ 收敛的实 σ 之下确界
(镜像 `LSeries.abscissaOfAbsConv`)。 -/
noncomputable def LaplaceData.abscissa (D : LaplaceData) : EReal :=
  sInf ((fun σ : ℝ => (σ : EReal)) '' {σ : ℝ | D.Converges σ})

/-- **半平面收敛**:`abscissa < σ ⟹ σ 收敛`。由下确界取一枚 `σ'' < σ` 且收敛,
再经单调性抬到 σ。此即 Laplace 变换于 `Re s > σ_c` 上良定义之根据。 -/
theorem LaplaceData.converges_of_abscissa_lt {D : LaplaceData} {σ : ℝ}
    (h : D.abscissa < (σ : EReal)) : D.Converges σ := by
  rw [LaplaceData.abscissa, sInf_lt_iff] at h
  obtain ⟨x, hx, hxσ⟩ := h
  obtain ⟨σ'', hσ''conv, rfl⟩ := hx
  have h2 : (σ'' : EReal) < (σ : EReal) := hxσ
  exact hσ''conv.mono (by exact_mod_cast h2.le)

/-- **半平面被积函数可积**:`abscissa < Re s` 时复被积函数 `u ↦ f(u) e^{-su}` 于
`[u₀,∞)` 绝对可积——故 `F(s)` 于 `Re s > σ_c` 真正良定义。其范数逐点等于实收敛
被积函数(`σ = Re s`)之范数,积分性由 `converges_of_abscissa_lt` 供给。此即
参数积分求导(F 全纯,源 F-7 A2)所需之 `hF_int` 假设。 -/
theorem LaplaceData.integrableOn_integrand {D : LaplaceData} {s : ℂ}
    (h : D.abscissa < (s.re : EReal)) :
    IntegrableOn (fun u => (D.f u : ℂ) * Complex.exp (-s * u)) (Ici D.u₀) := by
  have hconv : D.Converges s.re := D.converges_of_abscissa_lt h
  have hmeas : AEStronglyMeasurable (fun u => (D.f u : ℂ) * Complex.exp (-s * u))
      (volume.restrict (Ici D.u₀)) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable D.measf).mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  refine hconv.norm.mono' hmeas ?_
  filter_upwards with u
  have hre : (-s * (u : ℂ)).re = -s.re * u := by simp [Complex.mul_re]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_exp, hre, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]

/-- 由 `abscissa < r`(r 实)取一枚**实数** `x` 严格介于:`abscissa < x < r`。
横标之间取中间实指数(供解析延拓的局部一致支配用)。 -/
theorem LaplaceData.exists_real_between {D : LaplaceData} {r : ℝ}
    (h : D.abscissa < (r : EReal)) : ∃ x : ℝ, D.abscissa < (x : EReal) ∧ x < r := by
  obtain ⟨c, hac, hcr⟩ := exists_between h
  have hcb : c ≠ ⊥ := ne_bot_of_gt hac
  have hct : c ≠ ⊤ := ne_top_of_lt hcr
  refine ⟨c.toReal, ?_, ?_⟩
  · rwa [EReal.coe_toReal hct hcb]
  · have : (c.toReal : EReal) < (r : EReal) := by rwa [EReal.coe_toReal hct hcb]
    exact_mod_cast this

/-- **F' 被积函数半平面可积(源 F-7 A2 域点核心)**:`0 ≤ u₀` 且 `abscissa < Re s` 时,
`u ↦ f(u)·(-u)·e^{-su}`(即 `∂_s` 之被积函数)于 `[u₀,∞)` 绝对可积。取
`abscissa < σ₂ < Re s`,`ε := Re s − σ₂ > 0`;于 `u ≥ u₀ ≥ 0` 有 `u ≤ (1/ε)e^{εu}`
(`Real.add_one_le_exp`),故 `|u|e^{-Re s·u} ≤ (1/ε)e^{-σ₂u}`,被 `(1/ε)·` 实收敛
被积函数(σ₂)支配。这是参数积分求导(F 全纯)所需之 `Integrable (F' x₀)` 假设。 -/
theorem LaplaceData.integrableOn_derivIntegrand {D : LaplaceData} {s : ℂ}
    (hu₀ : 0 ≤ D.u₀) (h : D.abscissa < (s.re : EReal)) :
    IntegrableOn (fun u => (D.f u : ℂ) * (-(u : ℂ)) * Complex.exp (-s * u)) (Ici D.u₀) := by
  obtain ⟨σ₂, hσ₂a, hσ₂s⟩ := D.exists_real_between h
  have hconv : D.Converges σ₂ := D.converges_of_abscissa_lt hσ₂a
  set ε : ℝ := s.re - σ₂ with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hmeas : AEStronglyMeasurable
      (fun u => (D.f u : ℂ) * (-(u : ℂ)) * Complex.exp (-s * u))
      (volume.restrict (Ici D.u₀)) :=
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable D.measf).mul
      (by fun_prop)).mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  refine (hconv.norm.const_mul (1 / ε)).mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ici]
  filter_upwards with u hu
  have hu0 : 0 ≤ u := le_trans hu₀ hu
  have hre : (-s * (u : ℂ)).re = -s.re * u := by simp [Complex.mul_re]
  have hpoly : u ≤ (1 / ε) * Real.exp (ε * u) := by
    have h1 : ε * u ≤ Real.exp (ε * u) := le_trans (by linarith) (Real.add_one_le_exp (ε * u))
    rw [one_div]
    calc u = ε⁻¹ * (ε * u) := by rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
      _ ≤ ε⁻¹ * Real.exp (ε * u) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hexpbound : |u| * Real.exp (-s.re * u) ≤ (1 / ε) * Real.exp (-σ₂ * u) := by
    rw [abs_of_nonneg hu0]
    calc u * Real.exp (-s.re * u)
        ≤ ((1 / ε) * Real.exp (ε * u)) * Real.exp (-s.re * u) :=
          mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = (1 / ε) * Real.exp (-σ₂ * u) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; rw [hεdef]; ring
  calc ‖(D.f u : ℂ) * (-(u : ℂ)) * Complex.exp (-s * u)‖
      = |D.f u| * |u| * Real.exp (-s.re * u) := by
        simp only [norm_mul, norm_neg, Complex.norm_real, Complex.norm_exp, hre,
          Real.norm_eq_abs]
    _ ≤ |D.f u| * ((1 / ε) * Real.exp (-σ₂ * u)) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hexpbound (abs_nonneg _)
    _ = (1 / ε) * ‖D.f u * Real.exp (-σ₂ * u)‖ := by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]; ring

/-- **Laplace 变换于收敛半平面全纯(源 F-7 A2)**:`0 ≤ u₀` 时 `F` 于
`{s | abscissa < Re s}` 复可微。参数积分求导(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`):
取 `abscissa < σ₂ < σ₁ < Re s₀`,邻域 `{σ₁ < Re}`;`∂_s` 被积函数 `f·(-u)·e^{-su}` 之模于
该邻域一致受 `(1/ε)‖f·e^{-σ₂·}‖`(`ε=σ₁−σ₂`)支配,后者可积;逐点复导数由 `HasDerivAt.cexp`
给出。此即 Landau 引擎所需之 F 全纯性。 -/
theorem LaplaceData.differentiableOn_F {D : LaplaceData} (hu₀ : 0 ≤ D.u₀) :
    DifferentiableOn ℂ D.F {s : ℂ | D.abscissa < (s.re : EReal)} := by
  intro s₀ hs₀
  simp only [Set.mem_setOf_eq] at hs₀
  show DifferentiableWithinAt ℂ
    (fun s => ∫ u in Ici D.u₀, (D.f u : ℂ) * Complex.exp (-s * u))
    {s : ℂ | D.abscissa < (s.re : EReal)} s₀
  obtain ⟨σ₁, hσ₁a, hσ₁s⟩ := D.exists_real_between hs₀
  obtain ⟨σ₂, hσ₂a, hσ₂1⟩ := D.exists_real_between hσ₁a
  have hconv : D.Converges σ₂ := D.converges_of_abscissa_lt hσ₂a
  set ε : ℝ := σ₁ - σ₂ with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hnb_mem : {z : ℂ | σ₁ < z.re} ∈ nhds s₀ :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσ₁s
  have hmeasF : ∀ x : ℂ, AEStronglyMeasurable
      (fun u => (D.f u : ℂ) * Complex.exp (-x * u)) (volume.restrict (Ici D.u₀)) := fun x =>
    (Complex.continuous_ofReal.comp_aestronglyMeasurable D.measf).mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable
      (fun u => (D.f u : ℂ) * (-(u : ℂ)) * Complex.exp (-s₀ * u)) (volume.restrict (Ici D.u₀)) :=
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable D.measf).mul (by fun_prop)).mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hpoly : ∀ u : ℝ, 0 ≤ u → u ≤ (1 / ε) * Real.exp (ε * u) := by
    intro u hu0
    have h1 : ε * u ≤ Real.exp (ε * u) := le_trans (by linarith) (Real.add_one_le_exp (ε * u))
    rw [one_div]
    calc u = ε⁻¹ * (ε * u) := by rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
      _ ≤ ε⁻¹ * Real.exp (ε * u) := mul_le_mul_of_nonneg_left h1 (by positivity)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s u => (D.f u : ℂ) * Complex.exp (-s * u))
    (F' := fun x u => (D.f u : ℂ) * (-(u : ℂ)) * Complex.exp (-x * u))
    (bound := fun u => (1 / ε) * ‖D.f u * Real.exp (-σ₂ * u)‖)
    hnb_mem (Filter.Eventually.of_forall hmeasF) (D.integrableOn_integrand hs₀) hmeasF'
    ?hbound (hconv.norm.const_mul (1 / ε)) ?hdiff).2.differentiableAt.differentiableWithinAt
  case hbound =>
    rw [ae_restrict_iff' measurableSet_Ici]
    filter_upwards with u hu
    intro x hx
    have hu0 : 0 ≤ u := le_trans hu₀ hu
    have hxσ₁ : σ₁ < x.re := hx
    have hre : (-x * (u : ℂ)).re = -x.re * u := by simp [Complex.mul_re]
    have hstep1 : Real.exp (-x.re * u) ≤ Real.exp (-σ₁ * u) :=
      Real.exp_le_exp.mpr (by nlinarith [hxσ₁, hu0])
    have hstep2 : |u| * Real.exp (-σ₁ * u) ≤ (1 / ε) * Real.exp (-σ₂ * u) := by
      rw [abs_of_nonneg hu0]
      calc u * Real.exp (-σ₁ * u)
          ≤ ((1 / ε) * Real.exp (ε * u)) * Real.exp (-σ₁ * u) :=
            mul_le_mul_of_nonneg_right (hpoly u hu0) (Real.exp_pos _).le
        _ = (1 / ε) * Real.exp (-σ₂ * u) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; rw [hεdef]; ring
    calc ‖(D.f u : ℂ) * (-(u : ℂ)) * Complex.exp (-x * u)‖
        = |D.f u| * |u| * Real.exp (-x.re * u) := by
          simp only [norm_mul, norm_neg, Complex.norm_real, Complex.norm_exp, hre, Real.norm_eq_abs]
      _ ≤ |D.f u| * (|u| * Real.exp (-σ₁ * u)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hstep1 (abs_nonneg _)) (abs_nonneg _)
      _ ≤ |D.f u| * ((1 / ε) * Real.exp (-σ₂ * u)) :=
          mul_le_mul_of_nonneg_left hstep2 (abs_nonneg _)
      _ = (1 / ε) * ‖D.f u * Real.exp (-σ₂ * u)‖ := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]; ring
  case hdiff =>
    rw [ae_restrict_iff' measurableSet_Ici]
    filter_upwards with u _hu
    intro x _hx
    have hinner : HasDerivAt (fun s : ℂ => -s * (u : ℂ)) (-(u : ℂ)) x := by
      simpa using ((hasDerivAt_id x).neg.mul_const (u : ℂ))
    have hd := (hinner.cexp).const_mul (D.f u : ℂ)
    convert hd using 1
    ring

end UnifiedTheory
