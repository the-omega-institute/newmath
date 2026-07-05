import UnifiedTheory.Arithmetic.Zeckendorf
import UnifiedTheory.Golden.PhiInt
import UnifiedTheory.PZG.Carrier

/-!
# ch6 双面长度 λ₊/λ₋ 与 β(定义 6.4)

单素数轴上的双面读数:`betaPhi w` 是词中各 Fibonacci 指标处 φ 幂之和(取值 `PhiInt`),
其两个实嵌入即膨胀面 `betaPlusReal`(Σφ^i)与收缩面 `betaMinusReal`(Σψ^i)。位表层
`λ₊/λ₋` 按 `Σ_p (β 面读数)·log p` 汇总。gap 恒等式 `toRealPlus x - toRealMinus x = x.b·√5`
(φ−ψ=√5)是定理 6.22 亏空整性的杠杆:双面差只看 φ 分量。
-/

namespace UnifiedTheory

namespace PhiInt

/-- 双面差只由 φ 分量决定:`(a+bφ)−(a+bψ) = b·√5`。 -/
theorem gapReal_eq (x : PhiInt) :
    toRealPlus x - toRealMinus x = (x.b : ℝ) * Real.sqrt 5 := by
  have h := Real.goldenRatio_sub_goldenConj
  simp only [toRealPlus, toRealMinus]
  linear_combination (x.b : ℝ) * h

/-- `φ^n = (F_{n+1}−F_n) + F_n·φ`,即 φ 幂的整数对分量恰为 Fibonacci 数。 -/
theorem phiPow_ab (n : ℕ) :
    (phiPow n).a = (Nat.fib (n + 1) : ℤ) - Nat.fib n ∧ (phiPow n).b = (Nat.fib n : ℤ) := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> simp [phiPow]
  | succ k ih =>
    obtain ⟨iha, ihb⟩ := ih
    have hb : (phiPow (k + 1)).b = (Nat.fib (k + 1) : ℤ) := by
      simp only [phiPow, mul_b, phi_a, phi_b, iha, ihb]
      push_cast; ring
    have ha : (phiPow (k + 1)).a = (Nat.fib (k + 2) : ℤ) - Nat.fib (k + 1) := by
      simp only [phiPow, mul_a, phi_a, phi_b, iha, ihb]
      have : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      push_cast [this]; ring
    exact ⟨ha, hb⟩

@[simp] theorem phiPow_b (n : ℕ) : (phiPow n).b = (Nat.fib n : ℤ) := (phiPow_ab n).2

end PhiInt

namespace AxisWord

/-- 双面 `PhiInt` 读数:词中各指标 φ 幂之和。 -/
def betaPhi (w : AxisWord) : PhiInt := (w.1.map PhiInt.phiPow).foldr (· + ·) 0

/-- 膨胀面长度 Σφ^i。 -/
noncomputable def betaPlusReal (w : AxisWord) : ℝ := (betaPhi w).toRealPlus
/-- 收缩面长度 Σψ^i。 -/
noncomputable def betaMinusReal (w : AxisWord) : ℝ := (betaPhi w).toRealMinus

/-- `betaPhi` 的 φ 分量恰为解码值:`Σ_i F_i = decode w`。 -/
@[simp] theorem betaPhi_b (w : AxisWord) : (betaPhi w).b = (w.decode : ℤ) := by
  unfold betaPhi decode
  induction w.1 with
  | nil => simp
  | cons i l ih => simp [PhiInt.add_b, ih]

/-- 双面差 = √5·解码(定理 6.22 的杠杆:两面之差只见解码值)。 -/
theorem betaPhi_gap (w : AxisWord) :
    betaPlusReal w - betaMinusReal w = Real.sqrt 5 * (w.decode : ℝ) := by
  simp only [betaPlusReal, betaMinusReal]
  rw [PhiInt.gapReal_eq, betaPhi_b]; push_cast; ring

end AxisWord

namespace PZGTable

/-- 位表膨胀面长度 λ₊ = Σ_p β₊(轴 p)·log p。 -/
noncomputable def lambdaPlus (z : PZGTable) : ℝ :=
  z.1.sum fun p w => AxisWord.betaPlusReal w * Real.log p

/-- 位表收缩面长度 λ₋ = Σ_p β₋(轴 p)·log p。 -/
noncomputable def lambdaMinus (z : PZGTable) : ℝ :=
  z.1.sum fun p w => AxisWord.betaMinusReal w * Real.log p

end PZGTable

end UnifiedTheory
