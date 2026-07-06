import UnifiedTheory.Golden.Deficit
import UnifiedTheory.Golden.BeattyDeficit
import UnifiedTheory.Arithmetic.Zeckendorf

/-!
# ch6.44 位移 Zeckendorf–Beatty 桥的代数半

无条件代数引理 `betaMinus_encode_eq`:收缩面读数 `β₋(encode v)` 恰等于位移 Zeckendorf 和
`Σ_{i∈encode v} fib(i+1)` 减去 `v·φ`。这是把条件桥 `ShiftedZeckendorfBeattyBridge` 约化到
既有 `MinusWindow` 窗口界的代数一步(逐项 `ψ^i = fib(i+1) − fib(i)·φ` + Zeckendorf 往返)。
-/

namespace UnifiedTheory

private theorem list_sum_cast_fib (l : List ℕ) :
    (l.map (fun i => (Nat.fib i : ℝ))).sum = ((l.map Nat.fib).sum : ℝ) := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

private theorem list_sum_map_sub_mul_right {α : Type} (l : List α)
    (f g : α → ℝ) (r : ℝ) :
    (l.map (fun i => f i - g i * r)).sum = (l.map f).sum - (l.map g).sum * r := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp [ih]
      ring

/-- **无条件代数引理**:`β₋(encode v) = (Σ_{i∈encode v} fib(i+1)) − v·φ`。
逐项 `ψ^i = fib(i+1) − fib(i)·φ`(经 `toRealMinus_phiPow` + `phiPow_ab` + `ψ=1−φ`),
求和用 Zeckendorf 往返 `decode(encode v)=v`。 -/
theorem betaMinus_encode_eq (v : ℕ) :
    AxisWord.betaMinusReal (AxisWord.encode v)
      = ((AxisWord.encode v).1.map (fun i => (Nat.fib (i + 1) : ℝ))).sum
        - (v : ℝ) * Real.goldenRatio := by
  let l := (AxisWord.encode v).1
  have hterm : ∀ i : ℕ, Real.goldenConj ^ i
      = (Nat.fib (i + 1) : ℝ) - (Nat.fib i : ℝ) * Real.goldenRatio := by
    intro i
    have hψ : Real.goldenConj = 1 - Real.goldenRatio := by
      have h := Real.goldenRatio_add_goldenConj
      linarith
    rw [← PhiInt.toRealMinus_phiPow i]
    simp only [PhiInt.toRealMinus]
    have ha := (PhiInt.phiPow_ab i).1
    have hb := (PhiInt.phiPow_ab i).2
    rw [ha, hb, hψ]
    push_cast
    ring
  have hmap :
      (l.map (fun i => Real.goldenConj ^ i)) =
        l.map (fun i => (Nat.fib (i + 1) : ℝ) - (Nat.fib i : ℝ) * Real.goldenRatio) := by
    exact List.map_congr_left (fun i _ => hterm i)
  have hdecode :
      (l.map (fun i => (Nat.fib i : ℝ))).sum = (v : ℝ) := by
    have hnat : (l.map Nat.fib).sum = v := by
      change (AxisWord.decode (AxisWord.encode v)) = v
      exact AxisWord.decode_encode v
    rw [list_sum_cast_fib l, hnat]
  rw [AxisWord.betaMinusReal_eq_sum]
  change (l.map (fun i => Real.goldenConj ^ i)).sum =
      (l.map (fun i => (Nat.fib (i + 1) : ℝ))).sum - (v : ℝ) * Real.goldenRatio
  rw [hmap, list_sum_map_sub_mul_right l (fun i => (Nat.fib (i + 1) : ℝ))
    (fun i => (Nat.fib i : ℝ)) Real.goldenRatio, hdecode]

end UnifiedTheory
