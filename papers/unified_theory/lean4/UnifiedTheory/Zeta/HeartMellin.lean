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

end UnifiedTheory
