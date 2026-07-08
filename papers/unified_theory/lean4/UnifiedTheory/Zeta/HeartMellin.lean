import Mathlib

namespace UnifiedTheory

open Filter Topology

/-- **可听窗 Mellin 变换** `g̃(s) = 4 sinh²(s/2)/s²`,`s=0` 取可去极限 `1`。 -/
noncomputable def gTilde (s : ℂ) : ℂ :=
  if s = 0 then 1 else 4 * Complex.sinh (s / 2) ^ 2 / s ^ 2

/-- `g̃(0) = 1`(去奇异定义值)。 -/
theorem gTilde_zero : gTilde 0 = 1 := by
  simp [gTilde]

/-- `s ≠ 0` 时 `g̃(s) = 4 sinh²(s/2)/s²`。 -/
theorem gTilde_eq_of_ne {s : ℂ} (hs : s ≠ 0) :
    gTilde s = 4 * Complex.sinh (s / 2) ^ 2 / s ^ 2 := by
  simp [gTilde, hs]

/-- **可去奇异极限**:`g̃(s) → 1`(s→0),故站二空、g̃(0)=1 为真极限值。 -/
theorem tendsto_gTilde_zero :
    Tendsto gTilde (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 1) := by
  have hslope :
      Tendsto (fun z : ℂ => Complex.sinh z / z) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    have hderiv : HasDerivAt Complex.sinh (1 : ℂ) 0 := by
      simpa [Complex.cosh_zero] using Complex.hasDerivAt_sinh (0 : ℂ)
    have h := hderiv.tendsto_slope
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp [slope, Complex.sinh_zero, div_eq_mul_inv, mul_comm]
  have hhalf :
      Tendsto (fun s : ℂ => s / 2) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun s : ℂ => s) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using h.div_const (2 : ℂ)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have hratio :
      Tendsto (fun s : ℂ => Complex.sinh (s / 2) / (s / 2))
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    exact hslope.comp hhalf
  have hsquare :
      Tendsto (fun s : ℂ => (Complex.sinh (s / 2) / (s / 2)) ^ 2)
        (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa using hratio.pow 2
  refine hsquare.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [gTilde_eq_of_ne hs]
  field_simp [hs]
  ring

/-- **可听窗于右半平面不灭(源 H.7 判据之解析核心)**:`Re s > 0 ⟹ g̃(s) ≠ 0`。
`g̃(s) = 4 sinh²(s/2)/s²` 之零点仅居 `sinh(s/2)` 之零 `s ∈ 2πiℤ`(纯虚轴,`Re = 0`),
故凡有正实部之 `s` 皆听得见。这是心脏原生 RH 判据(H.7)反向证明的关键:每枚离线零点
`ρ* = β+iγ*`(`β>0`)必被某只环形电极听见,因 `g̃(ρ*) ≠ 0`。 -/
theorem gTilde_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : gTilde s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  rw [gTilde_eq_of_ne hs0]
  have hsinh : Complex.sinh (s / 2) ≠ 0 := by
    intro h
    have hf : Complex.sinh (s / 2) = (Complex.exp (s / 2) - Complex.exp (-(s / 2))) / 2 := rfl
    rw [hf] at h
    have h2 : Complex.exp (s / 2) = Complex.exp (-(s / 2)) := by
      have hz : Complex.exp (s / 2) - Complex.exp (-(s / 2)) = 0 := by
        field_simp at h; linear_combination h
      linear_combination hz
    have hexp : Complex.exp s = 1 := by
      have e1 : Complex.exp s = Complex.exp (s / 2) * Complex.exp (s / 2) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [e1]
      nth_rewrite 2 [h2]
      rw [← Complex.exp_add, show s / 2 + -(s / 2) = 0 by ring, Complex.exp_zero]
    rw [Complex.exp_eq_one_iff] at hexp
    obtain ⟨n, hn⟩ := hexp
    rw [hn] at hs
    simp at hs
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ hsinh)
  · exact pow_ne_zero _ hs0

/-- `‖sinh z‖ ≤ cosh(Re z)`(三角不等式于 `sinh z = (e^z − e^{−z})/2` + `‖e^z‖ = e^{Re z}`)。 -/
theorem norm_sinh_le_cosh_re (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.cosh z.re := by
  have hf : Complex.sinh z = (Complex.exp z - Complex.exp (-z)) / 2 := rfl
  rw [hf, norm_div, Complex.norm_ofNat, Real.cosh_eq,
    div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
  calc ‖Complex.exp z - Complex.exp (-z)‖
      ≤ ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := norm_sub_le _ _
    _ = Real.exp z.re + Real.exp (-z.re) := by
        rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]

/-- **可听窗于临界线之衰减(源 F-1)**:`‖g̃(½+iγ)‖ ≤ 4cosh²(¼)/γ²`——`O(γ⁻²)` 衰减,
故站三(零点站)之谱和逐项受控。证:`sinh(s/2)` 之模于 `Re(s/2)=¼` 上有界 `≤ cosh(¼)`,
而 `‖s‖² ≥ (Im s)² = γ²`。 -/
theorem gTilde_critical_line_decay (γ : ℝ) (hγ : γ ≠ 0) :
    ‖gTilde (1 / 2 + γ * Complex.I)‖ ≤ 4 * Real.cosh (1 / 4) ^ 2 / γ ^ 2 := by
  set s : ℂ := 1 / 2 + γ * Complex.I with hsdef
  have hsre : s.re = 1 / 2 := by simp [hsdef]
  have hsim : s.im = γ := by simp [hsdef]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hsim
    exact hγ hsim.symm
  have hhalf : (s / 2).re = 1 / 4 := by
    rw [Complex.div_re]; simp [hsre, hsim, Complex.normSq]; ring
  have hsinhbound : ‖Complex.sinh (s / 2)‖ ≤ Real.cosh (1 / 4) := by
    rw [← hhalf]; exact norm_sinh_le_cosh_re _
  have hsge : γ ^ 2 ≤ ‖s‖ ^ 2 := by
    have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    rw [hsim] at him
    nlinarith [him, abs_nonneg γ, sq_abs γ, norm_nonneg s]
  rw [gTilde_eq_of_ne hs0, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_ofNat]
  gcongr

end UnifiedTheory
