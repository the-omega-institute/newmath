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

/-- 把条件桥 `ShiftedZeckendorfBeattyBridge` 约化到既有窗口界 `MinusWindow`——合流两条
conditional 为一条(此后只需证 `MinusWindow` 即可无条件卸桥)。 -/
theorem shiftedZeckendorf_of_minusWindow (hwin : MinusWindow) :
    ShiftedZeckendorfBeattyBridge := by
  intro v
  let Sh : ℤ := ((AxisWord.encode v).1.map fun i => (Nat.fib (i + 1) : ℤ)).sum
  let β : ℝ := AxisWord.betaMinusReal (AxisWord.encode v)
  let ShR : ℝ := ((AxisWord.encode v).1.map fun i => (Nat.fib (i + 1) : ℝ)).sum
  have hβ : β = ShR - (v : ℝ) * Real.goldenRatio := by
    dsimp [β, ShR]
    exact betaMinus_encode_eq v
  have hcast : (Sh : ℝ) = ShR := by
    dsimp [Sh, ShR]
    induction (AxisWord.encode v).1 with
    | nil => simp
    | cons i l ih => simp [ih]
  obtain ⟨hlo, hup⟩ := hwin v
  have hloβ : -(1 / Real.goldenRatio ^ 2) < β := by simpa [β] using hlo
  have hupβ : β < 1 / Real.goldenRatio := by simpa [β] using hup
  have hφpos : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hinvφ : 1 / Real.goldenRatio = Real.goldenRatio - 1 := by
    rw [div_eq_iff (ne_of_gt hφpos)]
    linear_combination -hsq
  have hinvφ2 : 1 / Real.goldenRatio ^ 2 = 2 - Real.goldenRatio := by
    rw [div_eq_iff (by positivity)]
    linear_combination (Real.goldenRatio - 1) * hsq
  rw [hinvφ] at hupβ
  rw [hinvφ2] at hloβ
  have harg : ((v : ℝ) + 1) * Real.goldenRatio = (Sh : ℝ) - β + Real.goldenRatio := by
    nlinarith [hβ, hcast]
  have hfloor : ⌊((v : ℝ) + 1) * Real.goldenRatio⌋ = Sh + 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [harg]
      push_cast
      linarith [hupβ]
    · rw [harg]
      push_cast
      linarith [hloβ]
  unfold S
  rw [hfloor]
  simp [Sh]

end UnifiedTheory
