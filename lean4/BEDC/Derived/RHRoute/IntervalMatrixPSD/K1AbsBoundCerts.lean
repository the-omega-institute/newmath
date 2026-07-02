import BEDC.Derived.RHRoute.IntervalMatrixPSD.PolyPanelAbsBound
import BEDC.Derived.RHRoute.IntervalMatrixPSD.QNatCalculator
import BEDC.Derived.RHRoute.IntervalMatrixPSD.ArchimedeanRationalCerts

/-
Concrete K1 zero-panel abs-bound certificate (loop: archimedean obligation, block 4).

Discharges the concrete-polynomial content of `KernelApproxCerts.K1ZeroPanelObligations`'s
`T1_abs_bound_zeroPanel` field as a standalone 0-axiom theorem:
`PolyAbsBoundSound K1_T zeroPanelLeft zeroPanelRight K1_T_abs_bound`, i.e. `|evalPoly K1_T t|
<= 1633/3072` for every `t` in the zero panel `[0, 1/8]`.

Route: `polyAbsBoundSound_of_endpoint` (block 2) reduces the panel bound to the endpoint
comparison `evalPoly (K1_T.map ratAbs) (1/8) <= 1633/3072`.  `K1_T = [1/2, 1/4, -1/48]`, so at
`t = 1/8` the abs-coefficient sum is `1/2 + 1/32 + 1/3072`.  Each term is bounded by a
`/3072` qNat via `qNat_crossLe` (block 1) after folding its product with `qNat_mul` (block 3),
then summed same-denominator with `qNat_add_same_den` (block 3): `1536 + 96 + 1 = 1633`.
All 0-axiom / propext-free.
-/

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD.K1AbsBoundCerts

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure
open BEDC.Derived.RHRoute.IntervalMatrixPSD
open BEDC.Derived.RHRoute.IntervalMatrixPSD.QNatCalculator
open BEDC.Derived.RHRoute.IntervalMatrixPSD.ArchimedeanRationalCerts
open BEDC.Derived.RHRoute.IntervalMatrixPSD.PolyPanelAbsBound

/-- `|qNat n m| = qNat n m` (RatEq): the located magnitude of a nonneg located rational. -/
private theorem ratAbs_qNat (n m : Nat) : RatEq (ratAbs (qNat n m)) (qNat n m) :=
  ratMagnitude_eq_self_of_nonneg (qNat_nonneg n m)

/-- Endpoint term `T0 = |1/2| * (1/8)^0 = 1/2`. -/
private theorem term0 :
    RatEq (ratMul (ratAbs (qNat 1 2)) (pow (qNat 1 8) 0)) (qNat 1 2) :=
  RatEq_trans _ _ _ (ratMul_one_right (ratAbs (qNat 1 2))) (ratAbs_qNat 1 2)

/-- Endpoint term `T1 = |1/4| * (1/8)^1 = 1/32`. -/
private theorem term1 :
    RatEq (ratMul (ratAbs (qNat 1 4)) (pow (qNat 1 8) 1)) (qNat 1 32) :=
  RatEq_trans _ _ _
    (ratMul_respects (ratAbs_qNat 1 4) (ratMul_one_right (qNat 1 8)))
    (qNat_mul (a := 1) (b := 4) (c := 1) (d := 8)
      (Nat.succ_pos 3) (Nat.succ_pos 7))

/-- Endpoint term `T2 = |-1/48| * (1/8)^2 = 1/3072`. -/
private theorem term2 :
    RatEq (ratMul (ratAbs (qInt (-1) 48)) (pow (qNat 1 8) 2)) (qNat 1 3072) := by
  have habs : RatEq (ratAbs (qInt (-1) 48)) (qNat 1 48) :=
    RatEq_trans _ _ _ (ratMagnitude_neg (qNat 1 48)) (ratAbs_qNat 1 48)
  have hpow : RatEq (pow (qNat 1 8) 2) (qNat 1 64) :=
    RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl (qNat 1 8)) (ratMul_one_right (qNat 1 8)))
      (qNat_mul (a := 1) (b := 8) (c := 1) (d := 8)
        (Nat.succ_pos 7) (Nat.succ_pos 7))
  exact RatEq_trans _ _ _
    (ratMul_respects habs hpow)
    (qNat_mul (a := 1) (b := 48) (c := 1) (d := 64)
      (Nat.succ_pos 47) (Nat.succ_pos 63))

/-- The endpoint comparison: `evalPoly (K1_T.map ratAbs) (1/8) <= 1633/3072`. -/
private theorem endpoint_le :
    ratLe (evalPoly (List.map ratAbs K1_T) (qNat 1 8)) K1_T_abs_bound := by
  -- bound each term by a /3072 qNat via qNat_crossLe
  have b0 : ratLe (ratMul (ratAbs (qNat 1 2)) (pow (qNat 1 8) 0)) (qNat 1536 3072) :=
    ratLe_respects (RatEq_symm term0) (RatEq_refl _)
      (qNat_crossLe (a := 1) (d1 := 2) (b := 1536) (d2 := 3072)
        (Nat.succ_pos 1) (Nat.succ_pos 3071) (by decide))
  have b1 : ratLe (ratMul (ratAbs (qNat 1 4)) (pow (qNat 1 8) 1)) (qNat 96 3072) :=
    ratLe_respects (RatEq_symm term1) (RatEq_refl _)
      (qNat_crossLe (a := 1) (d1 := 32) (b := 96) (d2 := 3072)
        (Nat.succ_pos 31) (Nat.succ_pos 3071) (by decide))
  have b2 : ratLe (ratMul (ratAbs (qInt (-1) 48)) (pow (qNat 1 8) 2)) (qNat 1 3072) :=
    ratLe_of_RatEq term2
  -- the trailing (T2 + 0) term
  have b2z :
      ratLe (ratAdd (ratMul (ratAbs (qInt (-1) 48)) (pow (qNat 1 8) 2)) ratZero)
        (qNat 1 3072) :=
    ratLe_respects (RatEq_symm (ratAdd_zero_right _)) (RatEq_refl _) b2
  -- sum of the term bounds (same denominator)
  have sumBound :
      ratLe
        (ratAdd (ratMul (ratAbs (qNat 1 2)) (pow (qNat 1 8) 0))
          (ratAdd (ratMul (ratAbs (qNat 1 4)) (pow (qNat 1 8) 1))
            (ratAdd (ratMul (ratAbs (qInt (-1) 48)) (pow (qNat 1 8) 2)) ratZero)))
        (ratAdd (qNat 1536 3072) (ratAdd (qNat 96 3072) (qNat 1 3072))) :=
    ratAdd_le_add b0 (ratAdd_le_add b1 b2z)
  -- fold the /3072 bounds: 96 + 1 = 97, 1536 + 97 = 1633
  have foldInner : RatEq (ratAdd (qNat 96 3072) (qNat 1 3072)) (qNat 97 3072) :=
    qNat_add_same_den (a := 96) (c := 1) (m := 3072) (Nat.succ_pos 3071)
  have foldOuter :
      RatEq (ratAdd (qNat 1536 3072) (qNat 97 3072)) (qNat 1633 3072) :=
    qNat_add_same_den (a := 1536) (c := 97) (m := 3072) (Nat.succ_pos 3071)
  have rhsFold :
      RatEq (ratAdd (qNat 1536 3072) (ratAdd (qNat 96 3072) (qNat 1 3072)))
        (qNat 1633 3072) :=
    RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl (qNat 1536 3072)) foldInner)
      foldOuter
  exact ratLe_trans sumBound (ratLe_of_RatEq rhsFold)

/-- Zero-panel abs bound for `K1_T`: the concrete content of
`K1ZeroPanelObligations.T1_abs_bound_zeroPanel`, discharged 0-axiom. -/
theorem K1_T_abs_bound_zeroPanel_cert :
    PolyAbsBoundSound K1_T zeroPanelLeft zeroPanelRight K1_T_abs_bound :=
  polyAbsBoundSound_of_endpoint K1_T zeroPanelLeft zeroPanelRight K1_T_abs_bound
    (ratLe_refl ratZero) (qNat_nonneg 1 8) endpoint_le

end BEDC.Derived.RHRoute.IntervalMatrixPSD.K1AbsBoundCerts
