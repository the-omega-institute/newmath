import UnifiedTheory.Arithmetic.Zeckendorf
import UnifiedTheory.Golden.PhiInt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# 黄金亏空的 Beatty-floor 路线

本文件给出进位亏空的 floor 证明路线。核心事实不依赖 Zeckendorf 归一化:
Beatty 读数的二阶上边界自动满足形式进位律,而二元亏空值由 floor 加法基本界
和 `1 < φ < 2` 压进 `{-1,0,1}`。
-/

namespace UnifiedTheory

/-- Beatty-floor 位移读数。 -/
noncomputable def S (v : ℕ) : ℤ :=
  ⌊((v : ℝ) + 1) * Real.goldenRatio⌋ - 1

/-- Beatty 读数的二元进位亏空。 -/
noncomputable def cDef (a b : ℕ) : ℤ :=
  S a + S b - S (a + b)

/-- floor 加法至多损失一个单位,这里记录成整数上下界。 -/
private theorem floor_add_error_bounds (x y : ℝ) :
    -1 ≤ (⌊x⌋ : ℤ) + ⌊y⌋ - ⌊x + y⌋ ∧
      (⌊x⌋ : ℤ) + ⌊y⌋ - ⌊x + y⌋ ≤ 0 := by
  have hle : (⌊x⌋ : ℤ) + ⌊y⌋ ≤ ⌊x + y⌋ := Int.le_floor_add x y
  have hge : (⌊x + y⌋ : ℤ) - 1 ≤ ⌊x⌋ + ⌊y⌋ := Int.le_floor_add_floor x y
  constructor <;> omega

/-- 给实数加 `φ` 时,整数 floor 前进一个或两个单位。 -/
private theorem floor_golden_shift_bounds (z : ℝ) :
    1 ≤ (⌊z + Real.goldenRatio⌋ : ℤ) - ⌊z⌋ ∧
      (⌊z + Real.goldenRatio⌋ : ℤ) - ⌊z⌋ ≤ 2 := by
  have hfloor_one : (⌊z + (1 : ℝ)⌋ : ℤ) = ⌊z⌋ + 1 := Int.floor_add_one z
  have hlow0 : (⌊z + (1 : ℝ)⌋ : ℤ) ≤ ⌊z + Real.goldenRatio⌋ := by
    exact Int.floor_le_floor (by linarith [Real.one_lt_goldenRatio])
  have hlow : (⌊z⌋ : ℤ) + 1 ≤ ⌊z + Real.goldenRatio⌋ := by
    simpa [hfloor_one] using hlow0
  have hfloor_two : (⌊z + (2 : ℝ)⌋ : ℤ) = ⌊z⌋ + 2 := by
    simp
  have hhigh0 : (⌊z + Real.goldenRatio⌋ : ℤ) ≤ ⌊z + (2 : ℝ)⌋ := by
    exact Int.floor_le_floor (by linarith [Real.goldenRatio_lt_two])
  have hhigh : (⌊z + Real.goldenRatio⌋ : ℤ) ≤ ⌊z⌋ + 2 := by
    simpa [hfloor_two] using hhigh0
  constructor <;> omega

/-- 进位守恒:Beatty 亏空是二元上边界,因此 `δ² = 0`。 -/
theorem carry_conservation (a b c : ℕ) :
    cDef a b + cDef (a + b) c = cDef a (b + c) + cDef b c := by
  unfold cDef
  simp [Nat.add_assoc]
  ring

/-- Beatty-floor 亏空恒为 `-1`,`0`,`1` 三值之一。 -/
theorem cDef_mem : ∀ a b : ℕ, cDef a b = -1 ∨ cDef a b = 0 ∨ cDef a b = 1 := by
  intro a b
  let φ : ℝ := Real.goldenRatio
  let x : ℝ := ((a : ℝ) + 1) * φ
  let y : ℝ := ((b : ℝ) + 1) * φ
  let z : ℝ := (((a + b : ℕ) : ℝ) + 1) * φ
  have hxy : x + y = z + φ := by
    dsimp [x, y, z, φ]
    push_cast
    ring
  have herr := floor_add_error_bounds x y
  have herr_low : -1 ≤ (⌊x⌋ : ℤ) + ⌊y⌋ - ⌊x + y⌋ := herr.1
  have herr_high : (⌊x⌋ : ℤ) + ⌊y⌋ - ⌊x + y⌋ ≤ 0 := herr.2
  have hshift := floor_golden_shift_bounds z
  have hshift_low : 1 ≤ (⌊x + y⌋ : ℤ) - ⌊z⌋ := by
    rw [hxy]
    exact hshift.1
  have hshift_high : (⌊x + y⌋ : ℤ) - ⌊z⌋ ≤ 2 := by
    rw [hxy]
    exact hshift.2
  have hc :
      cDef a b =
        ((⌊x⌋ : ℤ) + ⌊y⌋ - ⌊x + y⌋) + ((⌊x + y⌋ : ℤ) - ⌊z⌋) - 1 := by
    dsimp [cDef, S, x, y, z, φ]
    push_cast
    ring
  omega

/-- Beatty 读数到位移 Zeckendorf 读数的条件桥。 -/
def ShiftedZeckendorfBeattyBridge : Prop :=
  ∀ v : ℕ, S v = ((AxisWord.encode v).1.map fun i => (Nat.fib (i + 1) : ℤ)).sum

/-- 任意条件桥证明都会立即给出 `S` 与位移 Zeckendorf 和的相等。 -/
theorem S_eq_shifted_zeck_of (h : ShiftedZeckendorfBeattyBridge) (v : ℕ) :
    S v = ((AxisWord.encode v).1.map fun i => (Nat.fib (i + 1) : ℤ)).sum :=
  h v

end UnifiedTheory
