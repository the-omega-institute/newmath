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

/-- On the real axis the complex Laplace transform is the complexification of the real integral. -/
theorem LaplaceData.F_ofReal (D : LaplaceData) (σ : ℝ) :
    D.F (σ : ℂ) =
      (∫ u in Ici D.u₀, D.f u * Real.exp (-σ * u) : ℝ) := by
  unfold LaplaceData.F
  rw [← integral_complex_ofReal]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
  intro u _hu
  change (D.f u : ℂ) * Complex.exp (-(σ : ℂ) * (u : ℂ)) =
    ((D.f u * Real.exp (-σ * u) : ℝ) : ℂ)
  have harg : -(σ : ℂ) * (u : ℂ) = ((-σ * u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

/-- Real part form of `F_ofReal`, convenient for sign estimates. -/
theorem LaplaceData.F_ofReal_re (D : LaplaceData) (σ : ℝ) :
    (D.F (σ : ℂ)).re = ∫ u in Ici D.u₀, D.f u * Real.exp (-σ * u) := by
  rw [LaplaceData.F_ofReal]
  simp

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

/-- A convergent real exponent lies to the right of the convergence abscissa. -/
theorem LaplaceData.abscissa_le_of_converges {D : LaplaceData} {σ : ℝ}
    (hσ : D.Converges σ) : D.abscissa ≤ (σ : EReal) := by
  rw [LaplaceData.abscissa]
  exact sInf_le ⟨σ, hσ, rfl⟩

/-- Strictly left of the convergence abscissa, the defining absolute convergence cannot hold. -/
theorem LaplaceData.not_converges_of_lt_abscissa {D : LaplaceData} {σ : ℝ}
    (hσ : (σ : EReal) < D.abscissa) : ¬ D.Converges σ := by
  intro hconv
  exact not_lt_of_ge (D.abscissa_le_of_converges hconv) hσ

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

/-- **Laplace 变换之显式一阶导(源 F-7 B1a 入口 / A2 强化)**:`0 ≤ u₀` 且
`abscissa < Re s₀` 时,`F` 于 `s₀` 复可导且导数即被积函数逐点求导的积分
`F'(s₀) = ∫_{u≥u₀} f(u)(-u)e^{-s₀u}`。参数积分求导
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`):取 `abscissa < σ₂ < σ₁ < Re s₀`,
邻域 `{σ₁ < Re}`;`∂_s` 被积函数 `f·(-u)·e^{-su}` 之模于该邻域一致受
`(1/ε)‖f·e^{-σ₂·}‖`(`ε=σ₁−σ₂`)支配,后者可积;逐点复导数由 `HasDerivAt.cexp` 给出。
这是 Landau 引擎逐阶导数(`(-1)^n F^{(n)}` 符号控制)的 `n=1` 底座。 -/
theorem LaplaceData.hasDerivAt_F {D : LaplaceData} (hu₀ : 0 ≤ D.u₀) {s₀ : ℂ}
    (hs₀ : D.abscissa < (s₀.re : EReal)) :
    HasDerivAt D.F
      (∫ u in Ici D.u₀, (D.f u : ℂ) * (-(u : ℂ)) * Complex.exp (-s₀ * u)) s₀ := by
  show HasDerivAt (fun s => ∫ u in Ici D.u₀, (D.f u : ℂ) * Complex.exp (-s * u))
    (∫ u in Ici D.u₀, (D.f u : ℂ) * (-(u : ℂ)) * Complex.exp (-s₀ * u)) s₀
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
    ?hbound (hconv.norm.const_mul (1 / ε)) ?hdiff).2
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

/-- **Laplace 变换于收敛半平面全纯(源 F-7 A2)**:`0 ≤ u₀` 时 `F` 于
`{s | abscissa < Re s}` 复可微。由显式一阶导 `hasDerivAt_F` 直接给出。 -/
theorem LaplaceData.differentiableOn_F {D : LaplaceData} (hu₀ : 0 ≤ D.u₀) :
    DifferentiableOn ℂ D.F {s : ℂ | D.abscissa < (s.re : EReal)} :=
  fun _s hs => (D.hasDerivAt_F hu₀ hs).differentiableAt.differentiableWithinAt

/-- **权重乘 `-u`**(供 Landau 引擎逐阶导数递归):`F^{(n+1)}` 即对权重 `(-u)^n f` 之
Laplace 变换再乘一层 `-u`。 -/
def LaplaceData.mulNegU (D : LaplaceData) : LaplaceData where
  f := fun u => (-u) * D.f u
  u₀ := D.u₀
  measf := (continuous_neg.aestronglyMeasurable).mul D.measf

/-- **乘 `-u` 保持收敛**:`0 ≤ u₀` 且 `abscissa < σ` 时 `mulNegU` 于 `σ` 收敛。
`|(-u)f e^{-σu}| = |u||f|e^{-σu} ≤ (1/ε)|f|e^{-σ₂u}`(`abscissa<σ₂<σ`,`ε=σ−σ₂`,
`u≤(1/ε)e^{εu}`),被实收敛被积函数(σ₂)支配——多项式因子不改横标。 -/
theorem LaplaceData.converges_mulNegU {D : LaplaceData} (hu₀ : 0 ≤ D.u₀) {σ : ℝ}
    (h : D.abscissa < (σ : EReal)) : (D.mulNegU).Converges σ := by
  obtain ⟨σ₂, hσ₂a, hσ₂s⟩ := D.exists_real_between h
  have hconv : D.Converges σ₂ := D.converges_of_abscissa_lt hσ₂a
  set ε : ℝ := σ - σ₂ with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  show IntegrableOn (fun u => ((-u) * D.f u) * Real.exp (-σ * u)) (Ici D.u₀)
  have hmeas : AEStronglyMeasurable (fun u => ((-u) * D.f u) * Real.exp (-σ * u))
      (volume.restrict (Ici D.u₀)) :=
    ((continuous_neg.aestronglyMeasurable).mul D.measf).mul
      (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  refine (hconv.norm.const_mul (1 / ε)).mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ici]
  filter_upwards with u hu
  have hu0 : 0 ≤ u := le_trans hu₀ hu
  have hpoly : u ≤ (1 / ε) * Real.exp (ε * u) := by
    have h1 : ε * u ≤ Real.exp (ε * u) := le_trans (by linarith) (Real.add_one_le_exp (ε * u))
    rw [one_div]
    calc u = ε⁻¹ * (ε * u) := by rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
      _ ≤ ε⁻¹ * Real.exp (ε * u) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hexpbound : |u| * Real.exp (-σ * u) ≤ (1 / ε) * Real.exp (-σ₂ * u) := by
    rw [abs_of_nonneg hu0]
    calc u * Real.exp (-σ * u)
        ≤ ((1 / ε) * Real.exp (ε * u)) * Real.exp (-σ * u) :=
          mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ = (1 / ε) * Real.exp (-σ₂ * u) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; rw [hεdef]; ring
  calc ‖((-u) * D.f u) * Real.exp (-σ * u)‖
      = |u| * |D.f u| * Real.exp (-σ * u) := by
        rw [norm_mul, norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.exp_pos _).le]
    _ = |D.f u| * (|u| * Real.exp (-σ * u)) := by ring
    _ ≤ |D.f u| * ((1 / ε) * Real.exp (-σ₂ * u)) :=
        mul_le_mul_of_nonneg_left hexpbound (abs_nonneg _)
    _ = (1 / ε) * ‖D.f u * Real.exp (-σ₂ * u)‖ := by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]; ring

/-- **乘 `-u` 后横标仍在同一半平面**:`abscissa < Re s ⟹ (mulNegU).abscissa < Re s`。
取 `abscissa < σ < Re s`,`mulNegU` 于 σ 收敛,故其横标 `≤ σ < Re s`。 -/
theorem LaplaceData.abscissa_mulNegU_lt {D : LaplaceData} (hu₀ : 0 ≤ D.u₀) {s : ℂ}
    (hs : D.abscissa < (s.re : EReal)) : (D.mulNegU).abscissa < (s.re : EReal) := by
  obtain ⟨σ, hσa, hσs⟩ := D.exists_real_between hs
  have hconv : (D.mulNegU).Converges σ := D.converges_mulNegU hu₀ hσa
  have hle : (D.mulNegU).abscissa ≤ (σ : EReal) :=
    sInf_le ⟨σ, hconv, rfl⟩
  exact lt_of_le_of_lt hle (by exact_mod_cast hσs)

/-- **导数即"权重乘 `-u`"之变换(B1 递归步)**:`abscissa < Re s ⟹ HasDerivAt F ((mulNegU).F s) s`。
`F'(s)=∫(-u)f e^{-su}` 恰为权重 `-u·f` 之 Laplace 变换 `(mulNegU).F s`。故 `F^{(n)}=(mulNegU^{[n]}).F`,
逐阶复用本引理 + `abscissa_mulNegU_lt`(每阶横标仍在半平面)即得迭代导数塔——无需 n 阶参数求导。 -/
theorem LaplaceData.hasDerivAt_F' {D : LaplaceData} (hu₀ : 0 ≤ D.u₀) {s : ℂ}
    (hs : D.abscissa < (s.re : EReal)) : HasDerivAt D.F ((D.mulNegU).F s) s := by
  have h := D.hasDerivAt_F hu₀ hs
  have hval : (D.mulNegU).F s
      = ∫ u in Ici D.u₀, (D.f u : ℂ) * (-(u : ℂ)) * Complex.exp (-s * u) := by
    show (∫ u in Ici D.u₀, ((D.mulNegU).f u : ℂ) * Complex.exp (-s * u)) = _
    apply setIntegral_congr_fun measurableSet_Ici
    intro u _
    show ((-u * D.f u : ℝ) : ℂ) * Complex.exp (-s * u)
      = (D.f u : ℂ) * (-(u : ℂ)) * Complex.exp (-s * u)
    push_cast; ring
  rw [hval]; exact h

/-- `mulNegU` 不改变 Laplace 数据的下端。 -/
theorem LaplaceData.u₀_iterate (D : LaplaceData) :
    ∀ n : ℕ, ((LaplaceData.mulNegU^[n]) D).u₀ = D.u₀ := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [Function.iterate_succ_apply', LaplaceData.mulNegU, ih]

/-- **逐阶横标保持**:反复乘 `-u` 后,收敛横标仍留在同一半平面内。 -/
theorem LaplaceData.abscissa_iterate_lt (D : LaplaceData) (hu₀ : 0 ≤ D.u₀) {s : ℂ}
    (hs : D.abscissa < (s.re : EReal)) :
    ∀ n : ℕ, ((LaplaceData.mulNegU^[n]) D).abscissa < (s.re : EReal) := by
  intro n
  induction n with
  | zero =>
      simpa using hs
  | succ n ih =>
      have hu₀n : 0 ≤ ((LaplaceData.mulNegU^[n]) D).u₀ := by
        rw [LaplaceData.u₀_iterate D n]
        exact hu₀
      have hstep := LaplaceData.abscissa_mulNegU_lt
        (D := ((LaplaceData.mulNegU^[n]) D)) hu₀n (s := s) ih
      simpa [Function.iterate_succ_apply'] using hstep

/-- **迭代导数塔闭式**:在收敛半平面内,
`F` 的第 `n` 阶导数等于权重连续乘 `-u` 后的 Laplace 变换。 -/
theorem LaplaceData.iteratedDeriv_F (D : LaplaceData) (hu₀ : 0 ≤ D.u₀) {s : ℂ}
    (hs : D.abscissa < (s.re : EReal)) :
    ∀ n : ℕ, iteratedDeriv n D.F s = ((LaplaceData.mulNegU^[n]) D).F s := by
  have hopen : IsOpen {z : ℂ | D.abscissa < (z.re : EReal)} := by
    have hcont : Continuous fun z : ℂ => (z.re : EReal) :=
      continuous_coe_real_ereal.comp Complex.continuous_re
    simpa [Set.preimage] using (isOpen_Ioi.preimage hcont : IsOpen
      ((fun z : ℂ => (z.re : EReal)) ⁻¹' Set.Ioi D.abscissa))
  have hlocal : ∀ n : ℕ, ∀ {z : ℂ},
      D.abscissa < (z.re : EReal) →
      iteratedDeriv n D.F z = ((LaplaceData.mulNegU^[n]) D).F z := by
    intro n
    induction n with
    | zero =>
        intro z _hz
        simp
    | succ n ih =>
        intro z hz
        rw [iteratedDeriv_succ]
        have heqOn : Set.EqOn (iteratedDeriv n D.F) (((LaplaceData.mulNegU^[n]) D).F)
            {w : ℂ | D.abscissa < (w.re : EReal)} := by
          intro w hw
          exact ih hw
        have hderiv_eq : deriv (iteratedDeriv n D.F) z =
            deriv (((LaplaceData.mulNegU^[n]) D).F) z :=
          (Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) heqOn).deriv_eq
        rw [hderiv_eq]
        have hu₀n : 0 ≤ ((LaplaceData.mulNegU^[n]) D).u₀ := by
          rw [LaplaceData.u₀_iterate D n]
          exact hu₀
        have habsn : ((LaplaceData.mulNegU^[n]) D).abscissa < (z.re : EReal) :=
          D.abscissa_iterate_lt hu₀ hz n
        calc
          deriv (((LaplaceData.mulNegU^[n]) D).F) z =
              (((LaplaceData.mulNegU^[n]) D).mulNegU).F z :=
            (LaplaceData.hasDerivAt_F' (D := ((LaplaceData.mulNegU^[n]) D))
              hu₀n habsn).deriv
          _ = ((LaplaceData.mulNegU^[n.succ]) D).F z := by
            simp [Function.iterate_succ_apply']
  intro n
  exact hlocal n hs

/-- 迭代乘 `-u` 后的权重闭式。 -/
theorem LaplaceData.f_iterate (D : LaplaceData) (n : ℕ) (u : ℝ) :
    ((LaplaceData.mulNegU^[n]) D).f u = (-u) ^ n * D.f u := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        ((LaplaceData.mulNegU^[n.succ]) D).f u
            = (-u) * ((LaplaceData.mulNegU^[n]) D).f u := by
              simp [Function.iterate_succ_apply', LaplaceData.mulNegU]
        _ = (-u) * ((-u) ^ n * D.f u) := by rw [ih]
        _ = (-u) ^ n.succ * D.f u := by
              rw [pow_succ]
              ring

/-- Landau 符号记账:非负权重给出实轴上交替迭代导数积分的非负性。 -/
theorem LaplaceData.sign_control (D : LaplaceData) (hu₀ : 0 ≤ D.u₀)
    (hf : ∀ u, D.u₀ ≤ u → 0 ≤ D.f u) {σ : ℝ}
    (hσ : D.abscissa < (σ : EReal)) (n : ℕ) :
    0 ≤ (-1) ^ n * ∫ u in Ici D.u₀,
      ((LaplaceData.mulNegU^[n]) D).f u * Real.exp (-σ * u) := by
  have _hσn : ((LaplaceData.mulNegU^[n]) D).abscissa < (σ : EReal) := by
    have hs : D.abscissa < (((σ : ℂ).re : ℝ) : EReal) := by
      simpa using hσ
    simpa using D.abscissa_iterate_lt hu₀ (s := (σ : ℂ)) hs n
  rw [← MeasureTheory.integral_const_mul]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ici (by
    intro u hu
    have huD : D.u₀ ≤ u := hu
    have hu_nonneg : 0 ≤ u := le_trans hu₀ huD
    have hf_nonneg : 0 ≤ D.f u := hf u huD
    have hpow_nonneg : 0 ≤ u ^ n := pow_nonneg hu_nonneg n
    have hexp_nonneg : 0 ≤ Real.exp (-σ * u) := Real.exp_nonneg _
    have hsign : (-1 : ℝ) ^ n * (-u) ^ n = u ^ n := by
      rw [← mul_pow]
      ring
    have hintegrand :
        (-1 : ℝ) ^ n *
            (((LaplaceData.mulNegU^[n]) D).f u * Real.exp (-σ * u))
          = u ^ n * D.f u * Real.exp (-σ * u) := by
      calc
        (-1 : ℝ) ^ n *
            (((LaplaceData.mulNegU^[n]) D).f u * Real.exp (-σ * u))
            = (-1 : ℝ) ^ n * (((-u) ^ n * D.f u) * Real.exp (-σ * u)) := by
              rw [LaplaceData.f_iterate]
        _ = (-1 : ℝ) ^ n * ((-u) ^ n * D.f u) * Real.exp (-σ * u) := by
              ring
        _ = ((-1 : ℝ) ^ n * (-u) ^ n) * D.f u * Real.exp (-σ * u) := by
              ring
        _ = u ^ n * D.f u * Real.exp (-σ * u) := by rw [hsign]
    rw [hintegrand]
    exact mul_nonneg (mul_nonneg hpow_nonneg hf_nonneg) hexp_nonneg)

/-- Complex-transform form of the Landau sign bookkeeping on the real axis. -/
theorem LaplaceData.sign_control_F (D : LaplaceData) (hu₀ : 0 ≤ D.u₀)
    (hf : ∀ u, D.u₀ ≤ u → 0 ≤ D.f u) {σ : ℝ}
    (hσ : D.abscissa < (σ : EReal)) (n : ℕ) :
    0 ≤ (-1) ^ n * (((LaplaceData.mulNegU^[n]) D).F (σ : ℂ)).re := by
  rw [LaplaceData.F_ofReal_re]
  rw [LaplaceData.u₀_iterate]
  exact D.sign_control hu₀ hf hσ n

/-- Alternating nonnegativity of the actual iterated derivatives of `F` on the real half-plane. -/
theorem LaplaceData.sign_control_iteratedDeriv_re (D : LaplaceData) (hu₀ : 0 ≤ D.u₀)
    (hf : ∀ u, D.u₀ ≤ u → 0 ≤ D.f u) {σ : ℝ}
    (hσ : D.abscissa < (σ : EReal)) (n : ℕ) :
    0 ≤ (-1) ^ n * (iteratedDeriv n D.F (σ : ℂ)).re := by
  have hs : D.abscissa < (((σ : ℂ).re : ℝ) : EReal) := by
    simpa using hσ
  rw [D.iteratedDeriv_F hu₀ hs n]
  exact D.sign_control_F hu₀ hf hσ n

/-- Polynomial weights are integrable on the real half-plane. -/
theorem LaplaceData.iter_weight_integrable (D : LaplaceData) (hu₀ : 0 ≤ D.u₀)
    {σ₁ : ℝ} (hσ₁ : D.abscissa < (σ₁ : EReal)) (n : ℕ) :
    IntegrableOn (fun u => u ^ n * D.f u * Real.exp (-σ₁ * u)) (Set.Ici D.u₀) := by
  have hs : D.abscissa < (((σ₁ : ℂ).re : ℝ) : EReal) := by
    simpa using hσ₁
  have hiter_abs :
      ((LaplaceData.mulNegU^[n]) D).abscissa < (σ₁ : EReal) := by
    simpa using D.abscissa_iterate_lt hu₀ (s := (σ₁ : ℂ)) hs n
  have hiter_conv : ((LaplaceData.mulNegU^[n]) D).Converges σ₁ :=
    LaplaceData.converges_of_abscissa_lt hiter_abs
  have hiter_on_D :
      IntegrableOn
        (fun u => ((LaplaceData.mulNegU^[n]) D).f u * Real.exp (-σ₁ * u))
        (Set.Ici D.u₀) := by
    simpa [LaplaceData.Converges, LaplaceData.u₀_iterate D n, neg_mul] using hiter_conv
  have hscaled :
      IntegrableOn
        (fun u =>
          (-1 : ℝ) ^ n *
            (((LaplaceData.mulNegU^[n]) D).f u * Real.exp (-σ₁ * u)))
        (Set.Ici D.u₀) :=
    hiter_on_D.const_mul ((-1 : ℝ) ^ n)
  refine hscaled.congr_fun ?_ measurableSet_Ici
  intro u _hu
  have hsign : (-1 : ℝ) ^ n * (-u) ^ n = u ^ n := by
    rw [← mul_pow]
    ring
  calc
    (-1 : ℝ) ^ n *
        (((LaplaceData.mulNegU^[n]) D).f u * Real.exp (-σ₁ * u))
        = (-1 : ℝ) ^ n * (((-u) ^ n * D.f u) * Real.exp (-σ₁ * u)) := by
          rw [LaplaceData.f_iterate D n u]
    _ = ((-1 : ℝ) ^ n * (-u) ^ n) * D.f u * Real.exp (-σ₁ * u) := by
          ring
    _ = u ^ n * D.f u * Real.exp (-σ₁ * u) := by
          rw [hsign]

/-- Each Taylor term built from the polynomial-weighted Laplace integrand is integrable. -/
theorem LaplaceData.taylor_term_integrable (D : LaplaceData) (hu₀ : 0 ≤ D.u₀)
    {σ₁ σ : ℝ} (hσ₁ : D.abscissa < (σ₁ : EReal)) (n : ℕ) :
    IntegrableOn (fun u => (σ₁ - σ) ^ n / (n.factorial : ℝ) *
      (u ^ n * D.f u * Real.exp (-σ₁ * u))) (Set.Ici D.u₀) :=
  (D.iter_weight_integrable hu₀ hσ₁ n).const_mul ((σ₁ - σ) ^ n / (n.factorial : ℝ))

/-- The Taylor terms around `σ₁` sum pointwise to the original real Laplace integrand. -/
theorem LaplaceData.taylor_series_pointwise (D : LaplaceData) (σ₁ σ : ℝ) (u : ℝ) :
    ∑' n : ℕ, (σ₁ - σ) ^ n / (n.factorial : ℝ) *
        (u ^ n * D.f u * Real.exp (-σ₁ * u))
      = D.f u * Real.exp (-σ * u) := by
  let C : ℝ := D.f u * Real.exp (-σ₁ * u)
  let x : ℝ := (σ₁ - σ) * u
  have hterm :
      (fun n : ℕ => (σ₁ - σ) ^ n / (n.factorial : ℝ) *
        (u ^ n * D.f u * Real.exp (-σ₁ * u))) =
      (fun n : ℕ => C * (x ^ n / (n.factorial : ℝ))) := by
    funext n
    simp [C, x, mul_pow, div_eq_mul_inv]
    ring_nf
  have hexp_series : (∑' n : ℕ, x ^ n / (n.factorial : ℝ)) = Real.exp x := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hterm, tsum_mul_left, hexp_series]
  calc
    C * Real.exp x = D.f u * (Real.exp (-σ₁ * u) * Real.exp ((σ₁ - σ) * u)) := by
      simp [C, x]
      ring_nf
    _ = D.f u * Real.exp (-σ * u) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf

/-- The nonnegative Taylor-term integrals are summable in norm. -/
theorem LaplaceData.taylor_summable_norm_integral (D : LaplaceData) (hu₀ : 0 ≤ D.u₀)
    (hf : ∀ u, D.u₀ ≤ u → 0 ≤ D.f u) {σ₁ σ : ℝ} (hσ₁ : D.abscissa < (σ₁ : EReal))
    (hlt : σ < σ₁)
    (hsum : Summable (fun n : ℕ => (σ₁ - σ) ^ n / (n.factorial : ℝ) *
        ∫ u in Set.Ici D.u₀, u ^ n * D.f u * Real.exp (-σ₁ * u))) :
    Summable (fun n : ℕ => ∫ u in Set.Ici D.u₀,
        ‖(σ₁ - σ) ^ n / (n.factorial : ℝ) * (u ^ n * D.f u * Real.exp (-σ₁ * u))‖) := by
  exact hsum.congr (fun n => by
    have _htaylor_integrable := D.taylor_term_integrable hu₀ (σ := σ) hσ₁ n
    have hc_nonneg : 0 ≤ (σ₁ - σ) ^ n / (n.factorial : ℝ) :=
      div_nonneg (pow_nonneg (sub_nonneg.mpr hlt.le) n) (by positivity)
    have hnorm :
        ∫ u in Set.Ici D.u₀,
            ‖(σ₁ - σ) ^ n / (n.factorial : ℝ) *
              (u ^ n * D.f u * Real.exp (-σ₁ * u))‖
          =
        ∫ u in Set.Ici D.u₀,
            (σ₁ - σ) ^ n / (n.factorial : ℝ) *
              (u ^ n * D.f u * Real.exp (-σ₁ * u)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
      intro u hu
      have hu_nonneg : 0 ≤ u := le_trans hu₀ hu
      have hterm_nonneg :
          0 ≤ (σ₁ - σ) ^ n / (n.factorial : ℝ) *
              (u ^ n * D.f u * Real.exp (-σ₁ * u)) := by
        have hweight_nonneg : 0 ≤ u ^ n * D.f u * Real.exp (-σ₁ * u) :=
          mul_nonneg (mul_nonneg (pow_nonneg hu_nonneg n) (hf u hu)) (Real.exp_nonneg _)
        exact mul_nonneg hc_nonneg hweight_nonneg
      exact Real.norm_of_nonneg hterm_nonneg
    have hconst :
        ∫ u in Set.Ici D.u₀,
            (σ₁ - σ) ^ n / (n.factorial : ℝ) *
              (u ^ n * D.f u * Real.exp (-σ₁ * u))
          =
        (σ₁ - σ) ^ n / (n.factorial : ℝ) *
          ∫ u in Set.Ici D.u₀, u ^ n * D.f u * Real.exp (-σ₁ * u) := by
      rw [MeasureTheory.integral_const_mul]
    exact (hnorm.trans hconst).symm)

/-- **Tonelli 级数-积分交换桥(F-7 Landau capstone)**:给定非负 Taylor 系数级数收敛
(`hsum`),Laplace 积分于 `σ < σ₁` 绝对收敛。三输入(逐项可积、逐点级数和、范数积分可和)
组装:`∫⁻‖f e^{-σu}‖ = ∫⁻‖∑ₙ Fₙ‖ ≤ ∫⁻ ∑ₙ‖Fₙ‖ = ∑ₙ∫⁻‖Fₙ‖ = ofReal(∑ₙ∫‖Fₙ‖) < ⊤`。 -/
theorem LaplaceData.converges_of_summable_taylor (D : LaplaceData) (hu₀ : 0 ≤ D.u₀)
    (hf : ∀ u, D.u₀ ≤ u → 0 ≤ D.f u) {σ₁ σ : ℝ} (hσ₁ : D.abscissa < (σ₁ : EReal))
    (hlt : σ < σ₁)
    (hsum : Summable (fun n : ℕ => (σ₁ - σ) ^ n / (n.factorial : ℝ) *
        ∫ u in Set.Ici D.u₀, u ^ n * D.f u * Real.exp (-σ₁ * u))) :
    D.Converges σ := by
  set μ : Measure ℝ := volume.restrict (Set.Ici D.u₀) with hμ
  set F : ℕ → ℝ → ℝ := fun n u =>
    (σ₁ - σ) ^ n / (n.factorial : ℝ) * (u ^ n * D.f u * Real.exp (-σ₁ * u)) with hFdef
  have hInt : ∀ n, Integrable (F n) μ := fun n => D.taylor_term_integrable hu₀ (σ := σ) hσ₁ n
  have hSum : Summable (fun n => ∫ u, ‖F n u‖ ∂μ) :=
    D.taylor_summable_norm_integral hu₀ hf hσ₁ hlt hsum
  have hptwise : ∀ u, (∑' n, F n u) = D.f u * Real.exp (-σ * u) :=
    fun u => D.taylor_series_pointwise σ₁ σ u
  have hmeas : AEStronglyMeasurable (fun u => D.f u * Real.exp (-σ * u)) μ :=
    D.measf.mul (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hbound : ∫⁻ u, ‖D.f u * Real.exp (-σ * u)‖ₑ ∂μ
      ≤ ENNReal.ofReal (∑' n, ∫ u, ‖F n u‖ ∂μ) := by
    calc ∫⁻ u, ‖D.f u * Real.exp (-σ * u)‖ₑ ∂μ
        = ∫⁻ u, ‖∑' n, F n u‖ₑ ∂μ := by
          refine lintegral_congr (fun u => ?_); rw [hptwise u]
      _ ≤ ∫⁻ u, ∑' n, ‖F n u‖ₑ ∂μ := lintegral_mono (fun u => enorm_tsum_le_tsum_enorm)
      _ = ∑' n, ∫⁻ u, ‖F n u‖ₑ ∂μ :=
          lintegral_tsum (fun n => (hInt n).aestronglyMeasurable.enorm)
      _ = ∑' n, ENNReal.ofReal (∫ u, ‖F n u‖ ∂μ) := by
          refine tsum_congr (fun n => ?_)
          rw [← ofReal_integral_norm_eq_lintegral_enorm (hInt n)]
      _ = ENNReal.ofReal (∑' n, ∫ u, ‖F n u‖ ∂μ) :=
          (ENNReal.ofReal_tsum_of_nonneg
            (fun n => integral_nonneg (fun u => norm_nonneg _)) hSum).symm
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top

/-- **Landau 反证核心**:若非负 Taylor 系数级数于某 `σ < σ_c` 收敛(`hsum`),则矛盾。
Tonelli 桥(`converges_of_summable_taylor`)由此给出 `Converges σ`,而横标定义
(`not_converges_of_lt_abscissa`)于 `σ < σ_c` 给出 `¬ Converges σ`。这是 Landau 振荡定理
反证的收尾一步;剩余开叶子是从边界解析延拓导出该 `hsum`(Taylor 半径-系数桥)。 -/
theorem LaplaceData.landau_contradiction (D : LaplaceData) (hu₀ : 0 ≤ D.u₀)
    (hf : ∀ u, D.u₀ ≤ u → 0 ≤ D.f u) {σ₁ σ : ℝ} (hσ₁ : D.abscissa < (σ₁ : EReal))
    (hσc : (σ : EReal) < D.abscissa)
    (hsum : Summable (fun n : ℕ => (σ₁ - σ) ^ n / (n.factorial : ℝ) *
        ∫ u in Set.Ici D.u₀, u ^ n * D.f u * Real.exp (-σ₁ * u))) :
    False := by
  have hlt : σ < σ₁ := by
    have h : (σ : EReal) < (σ₁ : EReal) := lt_trans hσc hσ₁
    exact_mod_cast h
  exact D.not_converges_of_lt_abscissa hσc
    (D.converges_of_summable_taylor hu₀ hf hσ₁ hlt hsum)

/-- **Taylor-系数桥(F 的幂级数系数 = 迭代 mulNegU 变换)**:若 `F` 于实点 `σ₁ > σ_c` 解析,
则其幂级数系数为 `(mulNegU^{[n]} D).F(σ₁)/n!`。合 mathlib `AnalyticAt.hasFPowerSeriesAt`
(系数 = `iteratedDeriv n F σ₁ / n!`)与迭代导数塔 `iteratedDeriv_F`。这是 `landau_nonneg`
剩余解析桥的系数一环;仍余半径 `> σ₁-σ_c` 与 `HasSum → hsum` 之实/复过渡。 -/
theorem LaplaceData.F_hasFPowerSeriesAt_mulNegU (D : LaplaceData) (hu₀ : 0 ≤ D.u₀)
    {σ₁ : ℝ} (hσ₁ : D.abscissa < (σ₁ : EReal)) (hA : AnalyticAt ℂ D.F (σ₁ : ℂ)) :
    HasFPowerSeriesAt D.F
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => ((LaplaceData.mulNegU^[n]) D).F (σ₁ : ℂ) / (n.factorial : ℂ))) (σ₁ : ℂ) := by
  have hcoeff : (fun n => iteratedDeriv n D.F (σ₁ : ℂ) / (n.factorial : ℂ))
      = (fun n => ((LaplaceData.mulNegU^[n]) D).F (σ₁ : ℂ) / (n.factorial : ℂ)) := by
    funext n
    rw [D.iteratedDeriv_F hu₀ (s := (σ₁ : ℂ)) (by simpa using hσ₁) n]
  have h1 := hA.hasFPowerSeriesAt
  rw [hcoeff] at h1
  exact h1

end UnifiedTheory
