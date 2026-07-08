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

end UnifiedTheory
