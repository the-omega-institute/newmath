import BEDC.Derived.RHRoute.IntervalMatrixPSD.KernelApproxCerts


/-
Rational-interval certificates for the archimedean K1 kernel budget (loop: archimedean
obligation, block 1).

Discharges the concrete-rational content of `KernelApproxCerts.K1ZeroPanelObligations`'s
`combined_error_le_eps` field, via a reusable 0-axiom bridge that was missing from the
tree: `qNat_crossLe` (rational comparison by integer cross-multiplication). No ∀-t /
located-Γ / RH content — purely the rational budget inequality
`ratLe K1_combined_error_bound K1_eps`, i.e.
`ratLe (qNat 94450105033 1541988050534400) (qNat 1 10000)`.

All proofs 0-axiom / propext-free: the Nat side is `Nat.le.intro` + `rfl`; the rational
side is BEDC located-division cancellation (`ratDivApart_mul_cancel_right`,
`ratMul_le_cancel_right`, `ratNat_mul`, `ratMul_respects_left/right`, RatEq transport).
Bridge proof shape from oracle conv_ff4ff126afd06e33 (collaborative).
-/

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD.ArchimedeanRationalCerts

open BEDC.Derived.RationalUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumLogEnclosure
open BEDC.Derived.RHRoute.IntervalMatrixPSD

/-- Transport `ratLe` along `RatEq` on both sides. -/
private theorem ratLe_congr {x x' y y' : Rat}
    (hx : RatEq x x') (hy : RatEq y y') (h : ratLe x' y') : ratLe x y :=
  ratLe_of_RatEq_right (ratLe_of_RatEq_left hx h) (RatEq_symm hy)

/-- `a·d2 ≤ b·d1` (Nat) lifts to `ratNat a · ratNat d2 ≤ ratNat b · ratNat d1`. -/
private theorem ratNat_mul_le_of_nat_mul_le {a d2 b d1 : Nat}
    (h : a * d2 ≤ b * d1) :
    ratLe (ratMul (ratNat a) (ratNat d2)) (ratMul (ratNat b) (ratNat d1)) :=
  ratLe_congr (ratNat_mul a d2) (ratNat_mul b d1) (ratNat_le_of_nat_le h)

/-- Positivity of `ratNat d1 · ratNat d2` for positive naturals. -/
private theorem ratNatMul_pos {d1 d2 : Nat} (hd1 : 0 < d1) (hd2 : 0 < d2) :
    ratLt ratZero (ratMul (ratNat d1) (ratNat d2)) :=
  ratLt_of_RatEq_right (ratNat_pos_of_pos (Nat.mul_pos hd1 hd2))
    (RatEq_symm (ratNat_mul d1 d2))

/-- `(x/d)·(d·e) = x·e`. -/
private theorem ratDivApart_mul_cancel_pair_right {x d e : Rat}
    (hd : ratApart0 d) :
    RatEq (ratMul (ratDivApart x d hd) (ratMul d e)) (ratMul x e) :=
  RatEq_trans _ _ _
    (RatEq_symm (ratMul_assoc (ratDivApart x d hd) d e))
    (ratMul_respects_left (ratDivApart_mul_cancel_right hd))

/-- `(x/e)·(d·e) = x·d`. -/
private theorem ratDivApart_mul_cancel_pair_cross_right {x d e : Rat}
    (he : ratApart0 e) :
    RatEq (ratMul (ratDivApart x e he) (ratMul d e)) (ratMul x d) :=
  RatEq_trans _ _ _
    (ratMul_respects_right (ratMul_comm d e))
    (ratDivApart_mul_cancel_pair_right (x := x) (d := e) (e := d) he)

/-- Fast cancel wrapper: explicit args form an opaque theorem boundary, so the
elaborator never whnf-expands the (ratNat / ratDivApart) structure during inference. -/
private theorem ratMul_le_cancel_right_fast (a b c : Rat)
    (hc : ratLt ratZero c) (h : ratLe (ratMul a c) (ratMul b c)) : ratLe a b :=
  ratMul_le_cancel_right hc h

/-- Rat-level division cross-comparison (variables only — the cancel sees only Rat
variables, so no big-term whnf blowup). -/
private theorem ratDivApart_crossLe_rat_fast {A B D1 D2 : Rat}
    (hD1 : ratApart0 D1) (hD2 : ratApart0 D2)
    (hCpos : ratLt ratZero (ratMul D1 D2))
    (hCross : ratLe (ratMul A D2) (ratMul B D1)) :
    ratLe (ratDivApart A D1 hD1) (ratDivApart B D2 hD2) := by
  have hLeftEq :
      RatEq (ratMul (ratDivApart A D1 hD1) (ratMul D1 D2)) (ratMul A D2) :=
    ratDivApart_mul_cancel_pair_right (x := A) (d := D1) (e := D2) hD1
  have hRightEq :
      RatEq (ratMul (ratDivApart B D2 hD2) (ratMul D1 D2)) (ratMul B D1) :=
    ratDivApart_mul_cancel_pair_cross_right (x := B) (d := D1) (e := D2) hD2
  have hScaled :
      ratLe (ratMul (ratDivApart A D1 hD1) (ratMul D1 D2))
        (ratMul (ratDivApart B D2 hD2) (ratMul D1 D2)) :=
    ratLe_congr hLeftEq hRightEq hCross
  exact ratMul_le_cancel_right_fast
    (ratDivApart A D1 hD1) (ratDivApart B D2 hD2) (ratMul D1 D2) hCpos hScaled

/-- Located-division comparison by integer cross-multiplication (thin Nat wrapper):
`a*d2 ≤ b*d1 → (ratNat a / ratNat d1) ≤ (ratNat b / ratNat d2)`. -/
theorem ratDivApart_crossLe_nat {a d1 b d2 : Nat}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (h : a * d2 ≤ b * d1) :
    ratLe
      (ratDivApart (ratNat a) (ratNat d1) (ratNat_apart0_of_pos hd1))
      (ratDivApart (ratNat b) (ratNat d2) (ratNat_apart0_of_pos hd2)) :=
  ratDivApart_crossLe_rat_fast
    (ratNat_apart0_of_pos hd1) (ratNat_apart0_of_pos hd2)
    (ratNatMul_pos hd1 hd2)
    (ratNat_mul_le_of_nat_mul_le h)

/-- Rational comparison of `qNat`s by integer cross-multiplication. Reusable bridge. -/
theorem qNat_crossLe {a d1 b d2 : Nat}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (h : a * d2 ≤ b * d1) :
    ratLe (qNat a d1) (qNat b d2) := by
  cases d1 with
  | zero => exact absurd hd1 (Nat.lt_irrefl 0)
  | succ d1' =>
      cases d2 with
      | zero => exact absurd hd2 (Nat.lt_irrefl 0)
      | succ d2' =>
          exact ratDivApart_crossLe_nat
            (Nat.succ_pos d1') (Nat.succ_pos d2') h

/-- The K1 combined-error budget inequality `K1_combined_error_bound ≤ K1_eps`
(the concrete-rational content of `K1ZeroPanelObligations.combined_error_le_eps`),
discharged 0-axiom. -/
theorem K1_combined_error_le_eps :
    ratLe (qNat 94450105033 1541988050534400) (qNat 1 10000) :=
  qNat_crossLe
    (a := 94450105033) (d1 := 1541988050534400)
    (b := 1) (d2 := 10000)
    (Nat.succ_pos 1541988050534399)
    (Nat.succ_pos 9999)
    (Nat.le.intro (rfl :
      94450105033 * 10000 + 597487000204400 = 1 * 1541988050534400))

end BEDC.Derived.RHRoute.IntervalMatrixPSD.ArchimedeanRationalCerts
