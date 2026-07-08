import UnifiedTheory.Golden.Lambda

/-!
# ch6 进位的双面账(命题 6.21)

归一化 `𝖭` 的重写规则在双面 (φ, ψ) 上的账目。**内部相邻规则 `11→100` 两面零亏空**:
`φ^i + φ^{i+1} = φ^{i+2}`(收缩面同),即 Fibonacci 递推作为动力学恒等;**底部规则带符号
单位亏空**:`2φ² − φ³ = 1`(由 φ³=2φ+1)。这些都是 φ²=φ+1 的有限代数推论。
-/

namespace UnifiedTheory
namespace Golden

open Real

/-- 命题 6.21 相邻进位(膨胀面,零亏空):`φ^i + φ^{i+1} = φ^{i+2}`。 -/
theorem gold_carry_plus (i : ℕ) :
    goldenRatio ^ i + goldenRatio ^ (i + 1) = goldenRatio ^ (i + 2) := by
  simp only [pow_succ]
  linear_combination (-(goldenRatio ^ i)) * Real.goldenRatio_sq

/-- 命题 6.21 相邻进位(收缩面,零亏空):`ψ^i + ψ^{i+1} = ψ^{i+2}`。 -/
theorem gold_carry_minus (i : ℕ) :
    goldenConj ^ i + goldenConj ^ (i + 1) = goldenConj ^ (i + 2) := by
  simp only [pow_succ]
  linear_combination (-(goldenConj ^ i)) * Real.goldenConj_sq

/-- 命题 6.21 底部规则(带符号单位亏空):`2φ² − φ³ = 1`。 -/
theorem gold_bottom_plus : 2 * goldenRatio ^ 2 - goldenRatio ^ 3 = 1 := by
  linear_combination (1 - goldenRatio) * Real.goldenRatio_sq

/-- 底部规则收缩面:`2ψ² − ψ³ = 1`。 -/
theorem gold_bottom_minus : 2 * goldenConj ^ 2 - goldenConj ^ 3 = 1 := by
  linear_combination (1 - goldenConj) * Real.goldenConj_sq

/-- 相邻进位在 `PhiInt` 上(两面同步精确保值):`φ^i + φ^{i+1} = φ^{i+2}`。 -/
theorem phiPow_carry (i : ℕ) :
    PhiInt.phiPow i + PhiInt.phiPow (i + 1) = PhiInt.phiPow (i + 2) := by
  rw [PhiInt.ext_iff]
  obtain ⟨ha0, hb0⟩ := PhiInt.phiPow_ab i
  obtain ⟨ha1, hb1⟩ := PhiInt.phiPow_ab (i + 1)
  obtain ⟨ha2, hb2⟩ := PhiInt.phiPow_ab (i + 2)
  refine ⟨?_, ?_⟩
  · simp only [PhiInt.add_a, ha0, ha1, ha2]
    have e1 : Nat.fib (i + 2) = Nat.fib i + Nat.fib (i + 1) := Nat.fib_add_two
    have e2 : Nat.fib (i + 3) = Nat.fib (i + 1) + Nat.fib (i + 2) := Nat.fib_add_two
    push_cast [e1, e2]; ring
  · simp only [PhiInt.add_b, hb0, hb1, hb2]
    have e1 : Nat.fib (i + 2) = Nat.fib i + Nat.fib (i + 1) := Nat.fib_add_two
    push_cast [e1]; ring

end Golden
end UnifiedTheory
