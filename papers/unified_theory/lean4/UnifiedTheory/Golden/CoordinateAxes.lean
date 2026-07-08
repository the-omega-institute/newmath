import UnifiedTheory.Golden.CoordinateSystem
import UnifiedTheory.Arithmetic.Zeckendorf
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# L1 coordinate axes for the golden coordinate system

This file adds the multiplicative-degree axis over `ℤ[φ]`, wires the
Zeckendorf digit axis to the existing `AxisWord` interface, and names the
geometric fractional coordinate.  The three-gap theorem for `{nφ}` is left as
an open leaf: mathlib does not currently provide it as a ready-made theorem.
-/

namespace UnifiedTheory
namespace PhiInt

/-- Multiplicative degree: logarithmic scale in base `φ`, rounded down. -/
noncomputable def degMul (x : PhiInt) : ℤ :=
  ⌊Real.logb Real.goldenRatio |toRealPlus x|⌋

/-- The powers `φ^n` sit exactly on integer multiplicative-degree levels. -/
@[simp] theorem degMul_phiPow (n : ℕ) : degMul (phiPow n) = n := by
  unfold degMul
  rw [toRealPlus_phiPow]
  have hpos : 0 < Real.goldenRatio ^ n := pow_pos Real.goldenRatio_pos n
  rw [abs_of_pos hpos]
  rw [Real.logb_pow, Real.logb_self_eq_one Real.one_lt_goldenRatio]
  simp

/-- Zeckendorf digits for the GCS digit axis, delegated to `AxisWord.encode`. -/
def zeckDigits (n : ℕ) : AxisWord :=
  AxisWord.encode n

/-- The digit-axis wrapper decodes back to the original natural number. -/
@[simp] theorem decode_zeckDigits (n : ℕ) : (zeckDigits n).decode = n :=
  AxisWord.decode_encode n

/-- Geometric fractional coordinate `{nφ}` for the GCS geometric axis. -/
noncomputable def geomCoord (n : ℕ) : ℝ :=
  Int.fract ((n : ℝ) * Real.goldenRatio)

end PhiInt
end UnifiedTheory
