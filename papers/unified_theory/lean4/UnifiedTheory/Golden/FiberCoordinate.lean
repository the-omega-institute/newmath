import Mathlib
import UnifiedTheory.Golden.BeattyDeficit
import UnifiedTheory.Golden.GoldenIdentities

namespace UnifiedTheory

open Real

local notation "BeattyShiftRead" => S

/-- **黄金取整桥**(源 6.48′):`⌊(v+1)φ⌋ = (v+1) + ⌊(v+1)/φ⌋`。
因 `φ = 1 + φ⁻¹` 且 `v+1` 为整,`(v+1)φ = (v+1) + (v+1)/φ`,整部分裂。 -/
theorem floorPhiMul_eq (v : ℕ) :
    ⌊((v : ℝ) + 1) * Real.goldenRatio⌋ = (v + 1 : ℤ) + ⌊((v : ℝ) + 1) / Real.goldenRatio⌋ := by
  have he :
      ((v : ℝ) + 1) * Real.goldenRatio =
        ((v + 1 : ℕ) : ℝ) + ((v : ℝ) + 1) / Real.goldenRatio := by
    have hinv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
      simpa [one_div] using goldenRatio_inv_eq
    rw [div_eq_mul_inv, hinv]
    push_cast
    ring
  rw [he]
  rw [Int.floor_natCast_add]
  push_cast
  ring

/-- **位移读数化为纤维坐标**(源 6.48′ 推论):`BeattyShiftRead v = v + ⌊(v+1)/φ⌋`。 -/
theorem beattyShiftRead_eq_add_floor (v : ℕ) :
    BeattyShiftRead v = (v : ℤ) + ⌊((v : ℝ) + 1) / Real.goldenRatio⌋ := by
  dsimp [S]
  rw [floorPhiMul_eq v]
  ring

end UnifiedTheory
