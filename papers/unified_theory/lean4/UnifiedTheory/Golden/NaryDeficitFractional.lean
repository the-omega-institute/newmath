import UnifiedTheory.Golden.NaryDeficit
import UnifiedTheory.Golden.DeficitFractional

namespace UnifiedTheory

/-- n 元亏空的 floor-τ 闭式(τ=φ−1)——
`Cn(vs)=Σ_i⌊(v_i+1)τ⌋ − ⌊(Σv_i+1)τ⌋`。整数部分相消,亏空纯由各项黄金旋转 τ 的分数部分决定;
是二元 `cDef_eq_floor_tau`(O1)的列表推广。 -/
theorem Cn_eq_floor_tau (vs : List ℕ) :
    Cn vs
      = (vs.map (fun v : ℕ => ⌊((v : ℝ) + 1) * (Real.goldenRatio - 1)⌋)).sum
        - ⌊((vs.sum : ℝ) + 1) * (Real.goldenRatio - 1)⌋ := by
  let g : ℕ → ℤ := fun v => ⌊((v : ℝ) + 1) * (Real.goldenRatio - 1)⌋
  change Cn vs = (vs.map g).sum - g vs.sum
  have hmap : vs.map S = vs.map (fun v : ℕ => (v : ℤ) + g v) := by
    apply List.map_congr_left
    intro v _
    simpa [g] using S_eq_tau v
  have hcast : (vs.map (fun v : ℕ => (v : ℤ))).sum = (vs.sum : ℤ) := by
    induction vs with
    | nil => simp
    | cons a as ih =>
        simp [Nat.cast_add]
  have hsumS : (vs.map S).sum = (vs.sum : ℤ) + (vs.map g).sum := by
    calc
      (vs.map S).sum = (vs.map (fun v : ℕ => (v : ℤ) + g v)).sum := by rw [hmap]
      _ = (vs.map (fun v : ℕ => (v : ℤ))).sum + (vs.map g).sum := by
        exact List.sum_map_add
      _ = (vs.sum : ℤ) + (vs.map g).sum := by rw [hcast]
  have hSsum : S vs.sum = (vs.sum : ℤ) + g vs.sum := by
    simpa [g] using S_eq_tau vs.sum
  unfold Cn
  rw [hsumS, hSsum]
  ring

end UnifiedTheory
