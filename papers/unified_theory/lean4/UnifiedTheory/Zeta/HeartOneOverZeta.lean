import Mathlib

namespace UnifiedTheory

open Filter Topology

/-- **1/ζ 于极点 s=1 取零**(源 H.1,"站二空"):ζ 在 `s=1` 有留数 1 的单极点,
故 `1/ζ(s) → 0`(s→1)。这是残余谱恒等式主项为净的解析输入。 -/
theorem one_div_riemannZeta_zero_at_one :
    Tendsto (fun s => (riemannZeta s)⁻¹) (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 0) := by
  have hres := riemannZeta_residue_one
  have hinv :
      Tendsto (fun s => ((s - 1) * riemannZeta s)⁻¹)
        (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (1 : ℂ)) := by
    have h := hres.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
    simpa using h
  have hsub :
      Tendsto (fun s : ℂ => s - 1) (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 0) := by
    have h :
        Tendsto (fun s : ℂ => s - 1) (nhds (1 : ℂ)) (nhds ((1 : ℂ) - 1)) :=
      (continuous_id.sub continuous_const).tendsto 1
    simpa using h.mono_left nhdsWithin_le_nhds
  have hprod :
      Tendsto (fun s : ℂ => (s - 1) * ((s - 1) * riemannZeta s)⁻¹)
        (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds 0) := by
    have h := hsub.mul hinv
    simpa using h
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
  have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

end UnifiedTheory
