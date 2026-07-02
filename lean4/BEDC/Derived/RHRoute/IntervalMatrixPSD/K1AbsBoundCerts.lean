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

/-- The `K1_A4` tail coefficients `[0, 1/6, 0, 1/120]` are all nonnegative. -/
private theorem A4_tail_coeffs_nonneg :
    ∀ c, c ∈ ([ratZero, qNat 1 6, ratZero, qNat 1 120] : List BRat) →
      ratLe ratZero c := by
  intro c hc
  -- eliminate the List.Mem inductive directly (propext-free; List.mem_cons Iff leaks propext)
  cases hc with
  | head => exact ratLe_refl ratZero
  | tail _ hc =>
    cases hc with
    | head => exact qNat_nonneg 1 6
    | tail _ hc =>
      cases hc with
      | head => exact ratLe_refl ratZero
      | tail _ hc =>
        cases hc with
        | head => exact qNat_nonneg 1 120
        | tail _ hc => nomatch hc

/-- Zero-panel lower bound for `K1_A4`: `1 <= evalPoly K1_A4 t` for every `t` in the zero
panel.  This is the concrete content of `K1ZeroPanelObligations.A_ge_one_zeroPanel` for the
natural rational carrier `A := fun t => evalPoly K1_A4 t` (K1_A4 = `1 + t^2/6 + t^4/120` has
constant term 1 and nonnegative higher coefficients, so it is `>= 1` at `t >= 0`).  0-axiom. -/
theorem K1_A4_ge_one_zeroPanel :
    ∀ t, inClosedPanel zeroPanelLeft zeroPanelRight t ->
      ratLe ratOne (evalPoly K1_A4 t) := by
  intro t ht
  have ht0 : ratLe ratZero t := ht.1
  have hrest :
      ratLe ratZero (evalShift 1 [ratZero, qNat 1 6, ratZero, qNat 1 120] t) :=
    evalShift_nonneg t ht0 [ratZero, qNat 1 6, ratZero, qNat 1 120]
      A4_tail_coeffs_nonneg 1
  have hhead : RatEq (ratMul ratOne (pow t 0)) ratOne := ratOne_mul_left ratOne
  have base :
      ratLe ratOne
        (ratAdd ratOne (evalShift 1 [ratZero, qNat 1 6, ratZero, qNat 1 120] t)) :=
    ratLe_respects (ratAdd_zero_right ratOne) (RatEq_refl _)
      (ratAdd_le_add (ratLe_refl ratOne) hrest)
  exact ratLe_respects (RatEq_refl ratOne)
    (ratAdd_respects (RatEq_symm hhead) (RatEq_refl _)) base

/-! ### `E1_4` zero-panel abs bound (degree 6)

`K1_E1_4 = [0, 0, 0, -1/32, 7/11520, -1/480, 1/5760]`, endpoint `t = 1/8`.  The three leading
zero coefficients contribute nothing; the four nonzero terms sum to
`92160 + 224 + 96 + 1 = 92481` over `1509949440 = 30827/503316480`, matching
`K1_E1_4_abs_bound`. -/

/-- Opaque boundary for `pow` succ-unfolding: proved at the Rat/Nat *variable* level so the
elaborator never whnf-reduces `ratPow` on the concrete big `qNat` term (block-1 whnf hazard). -/
private theorem pow_succ_eq (x : Rat) (n : Nat) :
    RatEq (pow x (Nat.succ n)) (ratMul (pow x n) x) := by
  change RatEq (ratMul (pow x n) x) (ratMul (pow x n) x)
  exact RatEq_refl _

/-- `(1/8)^k` folded to a single `qNat`, built up one factor of `1/8` at a time via
`qNat_mul`, routing each succ-step through `pow_succ_eq` to avoid whnf blowup.  `pow` is
x-right: `pow x (n+1) = (pow x n) * x`. -/
private theorem powE1 : RatEq (pow (qNat 1 8) 1) (qNat 1 8) :=
  RatEq_trans _ _ _ (pow_succ_eq (qNat 1 8) 0) (ratOne_mul_left (qNat 1 8))
private theorem powE2 : RatEq (pow (qNat 1 8) 2) (qNat 1 64) :=
  RatEq_trans _ _ _ (pow_succ_eq (qNat 1 8) 1)
    (RatEq_trans _ _ _ (ratMul_respects powE1 (RatEq_refl (qNat 1 8)))
      (qNat_mul (Nat.succ_pos 7) (Nat.succ_pos 7)))
private theorem powE3 : RatEq (pow (qNat 1 8) 3) (qNat 1 512) :=
  RatEq_trans _ _ _ (pow_succ_eq (qNat 1 8) 2)
    (RatEq_trans _ _ _ (ratMul_respects powE2 (RatEq_refl (qNat 1 8)))
      (qNat_mul (Nat.succ_pos 63) (Nat.succ_pos 7)))
private theorem powE4 : RatEq (pow (qNat 1 8) 4) (qNat 1 4096) :=
  RatEq_trans _ _ _ (pow_succ_eq (qNat 1 8) 3)
    (RatEq_trans _ _ _ (ratMul_respects powE3 (RatEq_refl (qNat 1 8)))
      (qNat_mul (Nat.succ_pos 511) (Nat.succ_pos 7)))
private theorem powE5 : RatEq (pow (qNat 1 8) 5) (qNat 1 32768) :=
  RatEq_trans _ _ _ (pow_succ_eq (qNat 1 8) 4)
    (RatEq_trans _ _ _ (ratMul_respects powE4 (RatEq_refl (qNat 1 8)))
      (qNat_mul (Nat.succ_pos 4095) (Nat.succ_pos 7)))
private theorem powE6 : RatEq (pow (qNat 1 8) 6) (qNat 1 262144) :=
  RatEq_trans _ _ _ (pow_succ_eq (qNat 1 8) 5)
    (RatEq_trans _ _ _ (ratMul_respects powE5 (RatEq_refl (qNat 1 8)))
      (qNat_mul (Nat.succ_pos 32767) (Nat.succ_pos 7)))

/-- Nonzero endpoint terms of `evalPoly (K1_E1_4.map ratAbs) (1/8)` as single qNats. -/
private theorem termE3 :
    RatEq (ratMul (ratAbs (qInt (-1) 32)) (pow (qNat 1 8) 3)) (qNat 1 16384) :=
  RatEq_trans _ _ _
    (ratMul_respects
      (RatEq_trans _ _ _ (ratMagnitude_neg (qNat 1 32)) (ratAbs_qNat 1 32)) powE3)
    (qNat_mul (Nat.succ_pos 31) (Nat.succ_pos 511))
private theorem termE4 :
    RatEq (ratMul (ratAbs (qNat 7 11520)) (pow (qNat 1 8) 4)) (qNat 7 47185920) :=
  RatEq_trans _ _ _ (ratMul_respects (ratAbs_qNat 7 11520) powE4)
    (qNat_mul (Nat.succ_pos 11519) (Nat.succ_pos 4095))
private theorem termE5 :
    RatEq (ratMul (ratAbs (qInt (-1) 480)) (pow (qNat 1 8) 5)) (qNat 1 15728640) :=
  RatEq_trans _ _ _
    (ratMul_respects
      (RatEq_trans _ _ _ (ratMagnitude_neg (qNat 1 480)) (ratAbs_qNat 1 480)) powE5)
    (qNat_mul (Nat.succ_pos 479) (Nat.succ_pos 32767))
private theorem termE6 :
    RatEq (ratMul (ratAbs (qNat 1 5760)) (pow (qNat 1 8) 6)) (qNat 1 1509949440) :=
  RatEq_trans _ _ _ (ratMul_respects (ratAbs_qNat 1 5760) powE6)
    (qNat_mul (Nat.succ_pos 5759) (Nat.succ_pos 262143))

/-- A leading zero-coefficient term vanishes: `|0| * (1/8)^k = 0`. -/
private theorem termE_zero (k : Nat) :
    RatEq (ratMul (ratAbs ratZero) (pow (qNat 1 8) k)) ratZero :=
  RatEq_trans _ _ _
    (ratMul_respects
      (ratMagnitude_eq_self_of_nonneg (ratLe_refl ratZero))
      (RatEq_refl (pow (qNat 1 8) k)))
    (ratMul_zero_left (pow (qNat 1 8) k))

/-- The endpoint comparison for `E1_4`:
`evalPoly (K1_E1_4.map ratAbs) (1/8) <= 30827/503316480`. -/
private theorem endpoint_le_E1_4 :
    ratLe (evalPoly (List.map ratAbs K1_E1_4) (qNat 1 8)) K1_E1_4_abs_bound := by
  -- nonzero part: term3 + (term4 + (term5 + (term6 + 0)))
  have b3 : ratLe (ratMul (ratAbs (qInt (-1) 32)) (pow (qNat 1 8) 3))
      (qNat 92160 1509949440) :=
    ratLe_respects (RatEq_symm termE3) (RatEq_refl _)
      (qNat_crossLe (Nat.succ_pos 16383) (Nat.succ_pos 1509949439) (by decide))
  have b4 : ratLe (ratMul (ratAbs (qNat 7 11520)) (pow (qNat 1 8) 4))
      (qNat 224 1509949440) :=
    ratLe_respects (RatEq_symm termE4) (RatEq_refl _)
      (qNat_crossLe (Nat.succ_pos 47185919) (Nat.succ_pos 1509949439) (by decide))
  have b5 : ratLe (ratMul (ratAbs (qInt (-1) 480)) (pow (qNat 1 8) 5))
      (qNat 96 1509949440) :=
    ratLe_respects (RatEq_symm termE5) (RatEq_refl _)
      (qNat_crossLe (Nat.succ_pos 15728639) (Nat.succ_pos 1509949439) (by decide))
  have b6 : ratLe (ratMul (ratAbs (qNat 1 5760)) (pow (qNat 1 8) 6))
      (qNat 1 1509949440) :=
    ratLe_of_RatEq termE6
  have b6z :
      ratLe (ratAdd (ratMul (ratAbs (qNat 1 5760)) (pow (qNat 1 8) 6)) ratZero)
        (qNat 1 1509949440) :=
    ratLe_respects (RatEq_symm (ratAdd_zero_right _)) (RatEq_refl _) b6
  have sumBound :
      ratLe
        (ratAdd (ratMul (ratAbs (qInt (-1) 32)) (pow (qNat 1 8) 3))
          (ratAdd (ratMul (ratAbs (qNat 7 11520)) (pow (qNat 1 8) 4))
            (ratAdd (ratMul (ratAbs (qInt (-1) 480)) (pow (qNat 1 8) 5))
              (ratAdd (ratMul (ratAbs (qNat 1 5760)) (pow (qNat 1 8) 6)) ratZero))))
        (ratAdd (qNat 92160 1509949440)
          (ratAdd (qNat 224 1509949440)
            (ratAdd (qNat 96 1509949440) (qNat 1 1509949440)))) :=
    ratAdd_le_add b3 (ratAdd_le_add b4 (ratAdd_le_add b5 b6z))
  -- fold the /1509949440 bounds: 96+1=97, 224+97=321, 92160+321=92481
  have rhsFold :
      RatEq
        (ratAdd (qNat 92160 1509949440)
          (ratAdd (qNat 224 1509949440)
            (ratAdd (qNat 96 1509949440) (qNat 1 1509949440))))
        (qNat 92481 1509949440) :=
    RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl (qNat 92160 1509949440))
        (ratAdd_respects (RatEq_refl (qNat 224 1509949440))
          (qNat_add_same_den (Nat.succ_pos 1509949439))))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl (qNat 92160 1509949440))
          (qNat_add_same_den (Nat.succ_pos 1509949439)))
        (qNat_add_same_den (Nat.succ_pos 1509949439)))
  have hnonzero :
      ratLe
        (ratAdd (ratMul (ratAbs (qInt (-1) 32)) (pow (qNat 1 8) 3))
          (ratAdd (ratMul (ratAbs (qNat 7 11520)) (pow (qNat 1 8) 4))
            (ratAdd (ratMul (ratAbs (qInt (-1) 480)) (pow (qNat 1 8) 5))
              (ratAdd (ratMul (ratAbs (qNat 1 5760)) (pow (qNat 1 8) 6)) ratZero))))
        (qNat 92481 1509949440) :=
    ratLe_respects (RatEq_refl _) rhsFold sumBound
  -- collapse the three leading zero terms
  have hcollapse :
      RatEq (evalPoly (List.map ratAbs K1_E1_4) (qNat 1 8))
        (ratAdd (ratMul (ratAbs (qInt (-1) 32)) (pow (qNat 1 8) 3))
          (ratAdd (ratMul (ratAbs (qNat 7 11520)) (pow (qNat 1 8) 4))
            (ratAdd (ratMul (ratAbs (qInt (-1) 480)) (pow (qNat 1 8) 5))
              (ratAdd (ratMul (ratAbs (qNat 1 5760)) (pow (qNat 1 8) 6)) ratZero)))) :=
    RatEq_trans _ _ _
      (ratAdd_respects (termE_zero 0) (RatEq_refl _))
      (RatEq_trans _ _ _
        (ratZero_add_left _)
        (RatEq_trans _ _ _
          (ratAdd_respects (termE_zero 1) (RatEq_refl _))
          (RatEq_trans _ _ _
            (ratZero_add_left _)
            (RatEq_trans _ _ _
              (ratAdd_respects (termE_zero 2) (RatEq_refl _))
              (ratZero_add_left _)))))
  exact ratLe_respects (RatEq_symm hcollapse) (RatEq_refl _)
    (ratLe_trans hnonzero
      (qNat_crossLe (Nat.succ_pos 1509949439) (Nat.succ_pos 503316479) (by decide)))

/-- Zero-panel abs bound for `K1_E1_4`: the concrete content of
`K1ZeroPanelObligations.E1_4_abs_bound_zeroPanel`, discharged 0-axiom. -/
theorem K1_E1_4_abs_bound_zeroPanel_cert :
    PolyAbsBoundSound K1_E1_4 zeroPanelLeft zeroPanelRight K1_E1_4_abs_bound :=
  polyAbsBoundSound_of_endpoint K1_E1_4 zeroPanelLeft zeroPanelRight K1_E1_4_abs_bound
    (ratLe_refl ratZero) (qNat_nonneg 1 8) endpoint_le_E1_4

end BEDC.Derived.RHRoute.IntervalMatrixPSD.K1AbsBoundCerts
