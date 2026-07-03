import BEDC.Derived.RHRoute.StripRationalKit
import BEDC.Derived.RHRoute.StripExclusionAssembly

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-!
Archimedean rational budget for the strip-exclusion assembly.

The two analytic inputs are left explicit: a rational upper bound for the
half-digamma term and a rational lower bound for the half-log-pi term.  This
file discharges the rational pole budget and the final addition/subtraction
chain against `StripExclusionAssembly.A_hi`.
-/

namespace BEDC.Derived.RHRoute.StripArchimedeanBound

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Real.RatNumKernel
open BEDC.Derived.RHRoute.StripRationalKit

abbrev Rat : Type :=
  RatNum

def sigma : Rat :=
  StripExclusionAssembly.sigma

def sigmaMinusOne : Rat :=
  qq 3 10

private theorem ratLe_congr {x x' y y' : Rat}
    (hx : RatEq x x') (hy : RatEq y y') (h : ratLe x' y') : ratLe x y :=
  ratLe_of_RatEq_right (ratLe_of_RatEq_left hx h) (RatEq_symm hy)

private theorem ratLt_respects_local {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> ratLt x y -> ratLt x' y' := by
  intro xx' yy' h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_respects xx' yy' (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects (RatEq_symm yy') (RatEq_symm xx') reverse)

private theorem ratAdd_nonneg {x y : Rat} :
    ratLe ratZero x -> ratLe ratZero y -> ratLe ratZero (ratAdd x y) := by
  intro hx hy
  have raw :
      ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    ratAdd_le_add hx hy
  exact ratLe_of_RatEq_left (ratZero_add_left ratZero) raw

private theorem ratLe_add_nonneg_right (x y : Rat)
    (hy : ratLe ratZero y) :
    ratLe x (ratAdd x y) := by
  have shifted : ratLe (ratAdd x ratZero) (ratAdd x y) := by
    exact BEDC.Derived.LocatedReal.ratLe_add_left_mono
      (y := ratZero) (y' := y) (x := x) hy
  exact ratLe_of_RatEq_left (RatEq_symm (ratAdd_zero_right x)) shifted

private theorem ratAdd_pos_of_pos_nonneg {x y : Rat} :
    ratLt ratZero x -> ratLe ratZero y -> ratLt ratZero (ratAdd x y) := by
  intro hx hy
  apply ratLe_not_le_to_ratLt
  · exact ratAdd_nonneg (ratLt_to_ratLe hx) hy
  · intro sumLeZero
    have xLeSum : ratLe x (ratAdd x y) :=
      ratLe_add_nonneg_right x y hy
    exact ratLt_not_ratLe_reverse hx (ratLe_trans xLeSum sumLeZero)

private theorem ratMul_pos_local {x y : Rat} :
    ratLt ratZero x -> ratLt ratZero y -> ratLt ratZero (ratMul x y) := by
  intro xPos yPos
  have raw : ratLt (ratMul x ratZero) (ratMul x y) :=
    ratMul_lt_mul_left yPos xPos
  have zeroRight : RatEq (ratMul x ratZero) ratZero := by
    unfold RatEq ratMul ratZero intToRat
    change
      IntEq (IntMul (IntMul x.num intZero) (ratDenInt ratZero))
        (IntMul intZero (ratDenInt (ratMul x ratZero)))
    exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
      (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))
  exact ratLt_respects_local zeroRight (RatEq_refl _) raw

private theorem ratLt_le_trans_local {x y z : Rat} :
    ratLt x y -> ratLe y z -> ratLt x z := by
  intro xy yz
  apply ratLe_not_le_to_ratLt
  · exact ratLe_trans (ratLt_to_ratLe xy) yz
  · intro zx
    exact ratLt_not_ratLe_reverse xy (ratLe_trans yz zx)

private theorem ratSquare_nonneg (x : Rat) :
    ratLe ratZero (ratMul x x) :=
  BEDC.Derived.RHRoute.JensenTuranDegree2.ratMul_self_nonneg x

private theorem ratSquare_pos_of_pos {x : Rat} :
    ratLt ratZero x -> ratLt ratZero (ratMul x x) :=
  fun hx => ratMul_pos_local hx hx

private theorem qq_pos {a b : Nat}
    (ha : 0 < a) (hb : 0 < b) :
    ratLt ratZero (qq a b hb) := by
  unfold qq StripExclusionAssembly.q
  exact BEDC.Derived.RationalOrderArithUp.div_pos
    (natRat_pos_of_pos ha) (natRat_pos_of_pos hb)

private theorem ratApart0_of_pos_local {x : Rat}
    (hx : ratLt ratZero x) : ratApart0 x :=
  ratPositive_num_nonzero hx

private theorem ratDivApart_respects {A A' D D' : Rat}
    (hD : ratApart0 D) (hD' : ratApart0 D')
    (hA : RatEq A A') (hDeq : RatEq D D') :
    RatEq (ratDivApart A D hD) (ratDivApart A' D' hD') := by
  have invRespects :
      RatEq (ratInvApart D hD) (ratInvApart D' hD') := by
    have invD :
        RatEq (ratMul (ratInvApart D hD) D) ratOne :=
      RatEq_trans _ _ _ (ratMul_comm (ratInvApart D hD) D)
        (ratInvApart_mul D hD)
    have dInvD' :
        RatEq (ratMul D' (ratInvApart D' hD')) ratOne :=
      ratInvApart_mul D' hD'
    exact RatEq_trans _ _ _
      (RatEq_symm (ratMul_one_right (ratInvApart D hD)))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl (ratInvApart D hD)) (RatEq_symm dInvD'))
        (RatEq_trans _ _ _
          (ratMul_respects (RatEq_refl (ratInvApart D hD))
            (ratMul_respects (RatEq_symm hDeq)
              (RatEq_refl (ratInvApart D' hD'))))
          (RatEq_trans _ _ _
            (RatEq_symm
              (ratMul_assoc (ratInvApart D hD) D
                (ratInvApart D' hD')))
            (RatEq_trans _ _ _
              (ratMul_respects invD (RatEq_refl (ratInvApart D' hD')))
              (ratOne_mul_left (ratInvApart D' hD'))))))
  unfold ratDivApart
  exact ratMul_respects hA invRespects

private theorem ratDivApart_mul {A D1 C D2 : Rat}
    (h1 : ratApart0 D1) (h2 : ratApart0 D2)
    (h12 : ratApart0 (ratMul D1 D2)) :
    RatEq (ratMul (ratDivApart A D1 h1) (ratDivApart C D2 h2))
      (ratDivApart (ratMul A C) (ratMul D1 D2) h12) := by
  unfold ratDivApart
  have invProduct :
      RatEq (ratInvApart (ratMul D1 D2) h12)
        (ratMul (ratInvApart D1 h1) (ratInvApart D2 h2)) :=
    ratInvApart_mul_product h1 h2 h12
  have regroup :
      RatEq
        (ratMul (ratMul A (ratInvApart D1 h1))
          (ratMul C (ratInvApart D2 h2)))
        (ratMul (ratMul A C)
          (ratMul (ratInvApart D1 h1) (ratInvApart D2 h2))) := by
    exact RatEq_trans _ _ _
      (ratMul_assoc A (ratInvApart D1 h1)
        (ratMul C (ratInvApart D2 h2)))
      (RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl A)
          (RatEq_trans _ _ _
            (RatEq_symm (ratMul_assoc (ratInvApart D1 h1) C
              (ratInvApart D2 h2)))
            (RatEq_trans _ _ _
              (ratMul_respects (ratMul_comm (ratInvApart D1 h1) C)
                (RatEq_refl (ratInvApart D2 h2)))
              (ratMul_assoc C (ratInvApart D1 h1)
                (ratInvApart D2 h2)))))
        (RatEq_symm (ratMul_assoc A C
          (ratMul (ratInvApart D1 h1) (ratInvApart D2 h2)))))
  exact RatEq_trans _ _ _ regroup
    (ratMul_respects (RatEq_refl (ratMul A C)) (RatEq_symm invProduct))

private theorem qq_mul {a b c d : Nat}
    (hb : 0 < b) (hd : 0 < d) :
    RatEq (ratMul (qq a b hb) (qq c d hd))
      (qq (a * c) (b * d) (Nat.mul_pos hb hd)) := by
  have h12 : ratApart0 (ratMul (natRat b) (natRat d)) :=
    ratMul_apart0 (natRat_apart0_of_pos hb) (natRat_apart0_of_pos hd)
  unfold qq StripExclusionAssembly.q
  exact RatEq_trans _ _ _
    (ratDivApart_mul (natRat_apart0_of_pos hb)
      (natRat_apart0_of_pos hd) h12)
    (RatEq_trans _ _ _
      (ratDivApart_respects h12
        (natRat_apart0_of_pos (Nat.mul_pos hb hd))
        (natRat_mul a c) (natRat_mul b d))
      (RatEq_refl _))

private theorem natRat_eq_qq_one (n : Nat) :
    RatEq (natRat n) (qq n 1) := by
  apply BEDC.Real.RatNumLogEnclosure.ratMul_right_cancel_apart0
    (c := natRat 1)
  · exact natRat_apart0_of_pos (by decide)
  · unfold qq StripExclusionAssembly.q
    have left : RatEq (ratMul (natRat n) (natRat 1)) (natRat n) :=
      ratMul_one_right (natRat n)
    have right :
        RatEq
          (ratMul
            (ratDivApart (natRat n) (natRat 1)
              (natRat_apart0_of_pos (by decide)))
            (natRat 1))
          (natRat n) :=
      ratDivApart_mul_cancel_right (natRat_apart0_of_pos (by decide))
    exact RatEq_trans _ _ _ left (RatEq_symm right)

private theorem ratSub_add_cancel_right (x y : Rat) :
    RatEq (ratAdd (ratSub x y) y) x := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x (ratNeg y) y)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratNeg_add_local y))
      (ratAdd_zero_right x))

private theorem ratAdd_right_neg_cancel (x y : Rat) :
    RatEq (ratAdd (ratAdd x y) (ratNeg y)) x := by
  exact RatEq_trans _ _ _
    (BEDC.Derived.LocatedReal.ratAdd_assoc_local x y (ratNeg y))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratAdd_neg_local y))
      (ratAdd_zero_right x))

private theorem ratSub_eq_of_add_right_eq {x y z : Rat} :
    RatEq (ratAdd x y) z -> RatEq (ratSub z y) x := by
  intro h
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_symm h) (RatEq_refl (ratNeg y)))
    (ratAdd_right_neg_cancel x y)

private theorem ratLe_neg_anti {a b : Rat} :
    ratLe a b -> ratLe (ratNeg b) (ratNeg a) := by
  intro h
  let t := ratAdd (ratNeg a) (ratNeg b)
  have shifted : ratLe (ratAdd a t) (ratAdd b t) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := a) (x' := b) (y := t) h
  have leftEq : RatEq (ratAdd a t) (ratNeg b) := by
    unfold t
    exact RatEq_trans _ _ _
      (RatEq_symm
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local
          a (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (ratAdd_respects
          (BEDC.Derived.LocatedReal.ratAdd_neg_local a)
          (RatEq_refl (ratNeg b)))
        (ratZero_add_left (ratNeg b)))
  have rightEq : RatEq (ratAdd b t) (ratNeg a) := by
    unfold t
    exact RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl b)
        (ratAdd_comm (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local
            b (ratNeg b) (ratNeg a)))
        (RatEq_trans _ _ _
          (ratAdd_respects
            (BEDC.Derived.LocatedReal.ratAdd_neg_local b)
            (RatEq_refl (ratNeg a)))
          (ratZero_add_left (ratNeg a))))
  exact ratLe_respects leftEq rightEq shifted

private theorem ratSub_le_sub_of_le_of_le {a b c d : Rat} :
    ratLe a b -> ratLe c d -> ratLe (ratSub a d) (ratSub b c) := by
  intro hab hcd
  exact ratAdd_le_add hab (ratLe_neg_anti hcd)

private theorem sigma_eq_qq :
    RatEq sigma (qq 13 10) := by
  unfold sigma StripExclusionAssembly.sigma qq
  exact qq_eq_of_cross (by decide) (by decide) (by decide)

private theorem sigma_pos :
    ratLt ratZero sigma := by
  have qPos : ratLt ratZero (qq 13 10) :=
    qq_pos (by decide) (by decide)
  exact ratLt_respects_local (RatEq_refl ratZero) (RatEq_symm sigma_eq_qq) qPos

private theorem sigma_nonneg :
    ratLe ratZero sigma :=
  ratLt_to_ratLe sigma_pos

private theorem sigmaMinusOne_pos :
    ratLt ratZero sigmaMinusOne :=
  qq_pos (by decide) (by decide)

private theorem sigmaMinusOne_nonneg :
    ratLe ratZero sigmaMinusOne :=
  ratLt_to_ratLe sigmaMinusOne_pos

private theorem sigma_sq_eq :
    RatEq (ratMul sigma sigma) (qq 169 100) := by
  have raw :
      RatEq (ratMul (qq 13 10) (qq 13 10)) (qq 169 100) :=
    qq_mul (a := 13) (b := 10) (c := 13) (d := 10)
      (by decide) (by decide)
  exact RatEq_trans _ _ _
    (ratMul_respects sigma_eq_qq sigma_eq_qq) raw

private theorem sigmaMinusOne_sq_eq :
    RatEq (ratMul sigmaMinusOne sigmaMinusOne) (qq 9 100) := by
  unfold sigmaMinusOne
  exact qq_mul (a := 3) (b := 10) (c := 3) (d := 10)
    (by decide) (by decide)

private theorem qq169_add_289_eq :
    RatEq (ratAdd (qq 169 100) (natRat 289)) (qq 29069 100) := by
  have h289 : RatEq (natRat 289) (qq 28900 100) :=
    RatEq_trans _ _ _
      (natRat_eq_qq_one 289)
      (qq_eq_of_cross (by decide) (by decide) (by decide))
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl _) h289)
    (qq_add_same_den (a := 169) (c := 28900) (m := 100) (by decide))

private theorem qq9_add_289_eq :
    RatEq (ratAdd (qq 9 100) (natRat 289)) (qq 28909 100) := by
  have h289 : RatEq (natRat 289) (qq 28900 100) :=
    RatEq_trans _ _ _
      (natRat_eq_qq_one 289)
      (qq_eq_of_cross (by decide) (by decide) (by decide))
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl _) h289)
    (qq_add_same_den (a := 9) (c := 28900) (m := 100) (by decide))

private theorem seventeen_sq_eq :
    RatEq (ratMul (natRat 17) (natRat 17)) (natRat 289) :=
  natRat_mul 17 17

private theorem square_ge_17_sq {t : Rat}
    (ht : ratLe (natRat 17) t) :
    ratLe (natRat 289) (ratMul t t) := by
  have h17Nonneg : ratLe ratZero (natRat 17) :=
    ratLt_to_ratLe (natRat_pos_of_pos (by decide))
  have htNonneg : ratLe ratZero t :=
    ratLe_trans h17Nonneg ht
  have sqLe :
      ratLe (ratMul (natRat 17) (natRat 17)) (ratMul t t) := by
    exact BEDC.Derived.RationalOrderArithUp.mul_le_mul_nonneg
      ht ht h17Nonneg h17Nonneg
  exact ratLe_of_RatEq_left seventeen_sq_eq sqLe

private theorem pole1_den_pos (t : Rat) :
    ratLt ratZero (ratAdd (ratMul sigma sigma) (ratMul t t)) :=
  ratAdd_pos_of_pos_nonneg
    (ratSquare_pos_of_pos sigma_pos)
    (ratSquare_nonneg t)

private theorem pole2_den_pos (t : Rat) :
    ratLt ratZero (ratAdd (ratMul sigmaMinusOne sigmaMinusOne) (ratMul t t)) :=
  ratAdd_pos_of_pos_nonneg
    (ratSquare_pos_of_pos sigmaMinusOne_pos)
    (ratSquare_nonneg t)

private theorem pole1_den_apart (t : Rat) :
    ratApart0 (ratAdd (ratMul sigma sigma) (ratMul t t)) :=
  ratApart0_of_pos_local (pole1_den_pos t)

private theorem pole2_den_apart (t : Rat) :
    ratApart0 (ratAdd (ratMul sigmaMinusOne sigmaMinusOne) (ratMul t t)) :=
  ratApart0_of_pos_local (pole2_den_pos t)

def pole1 (t : Rat) : Rat :=
  ratDivApart sigma
    (ratAdd (ratMul sigma sigma) (ratMul t t))
    (pole1_den_apart t)

def pole2 (t : Rat) : Rat :=
  ratDivApart sigmaMinusOne
    (ratAdd (ratMul sigmaMinusOne sigmaMinusOne) (ratMul t t))
    (pole2_den_apart t)

private theorem pole1_baseline_den_le {t : Rat}
    (ht : ratLe (natRat 17) t) :
    ratLe (qq 29069 100)
      (ratAdd (ratMul sigma sigma) (ratMul t t)) := by
  have tail : ratLe (natRat 289) (ratMul t t) :=
    square_ge_17_sq ht
  have raw :
      ratLe (ratAdd (qq 169 100) (natRat 289))
        (ratAdd (ratMul sigma sigma) (ratMul t t)) :=
    ratAdd_le_add
      (ratLe_of_RatEq (RatEq_symm sigma_sq_eq))
      tail
  exact ratLe_of_RatEq_left (RatEq_symm qq169_add_289_eq) raw

private theorem pole2_baseline_den_le {t : Rat}
    (ht : ratLe (natRat 17) t) :
    ratLe (qq 28909 100)
      (ratAdd (ratMul sigmaMinusOne sigmaMinusOne) (ratMul t t)) := by
  have tail : ratLe (natRat 289) (ratMul t t) :=
    square_ge_17_sq ht
  have raw :
      ratLe (ratAdd (qq 9 100) (natRat 289))
        (ratAdd (ratMul sigmaMinusOne sigmaMinusOne) (ratMul t t)) :=
    ratAdd_le_add
      (ratLe_of_RatEq (RatEq_symm sigmaMinusOne_sq_eq))
      tail
  exact ratLe_of_RatEq_left (RatEq_symm qq9_add_289_eq) raw

private theorem qq_29069_pos :
    ratLt ratZero (qq 29069 100) :=
  qq_pos (by decide) (by decide)

private theorem qq_28909_pos :
    ratLt ratZero (qq 28909 100) :=
  qq_pos (by decide) (by decide)

private theorem qq_29069_apart :
    ratApart0 (qq 29069 100) :=
  ratApart0_of_pos_local qq_29069_pos

private theorem qq_28909_apart :
    ratApart0 (qq 28909 100) :=
  ratApart0_of_pos_local qq_28909_pos

private theorem sigma_over_baseline_eq :
    RatEq
      (ratDivApart sigma (qq 29069 100) qq_29069_apart)
      (qq 130 29069) := by
  have numerator :
      RatEq
        (ratDivApart sigma (qq 29069 100) qq_29069_apart)
        (ratDivApart (qq 13 10) (qq 29069 100) qq_29069_apart) :=
    ratDivApart_respects qq_29069_apart qq_29069_apart
      sigma_eq_qq (RatEq_refl _)
  have divEq :
      RatEq
        (ratDivApart (qq 13 10) (qq 29069 100) qq_29069_apart)
        (qq 130 29069) := by
    have leftCancel :
          RatEq
            (ratMul
              (ratDivApart (qq 13 10) (qq 29069 100) qq_29069_apart)
              (qq 29069 100))
            (qq 13 10) :=
        ratDivApart_mul_cancel_right qq_29069_apart
    have rightProduct :
          RatEq (ratMul (qq 130 29069) (qq 29069 100))
            (qq 13 10) := by
        exact RatEq_trans _ _ _
          (qq_mul (a := 130) (b := 29069) (c := 29069) (d := 100)
            (by decide) (by decide))
          (qq_eq_of_cross (by decide) (by decide) (by decide))
    exact BEDC.Real.RatNumLogEnclosure.ratMul_right_cancel_apart0
      (ratDivApart (qq 13 10) (qq 29069 100) qq_29069_apart)
      (qq 130 29069)
      (qq 29069 100)
      qq_29069_apart
      (RatEq_trans _ _ _ leftCancel (RatEq_symm rightProduct))
  exact RatEq_trans _ _ _ numerator divEq

private theorem sigmaMinusOne_over_baseline_eq :
    RatEq
      (ratDivApart sigmaMinusOne (qq 28909 100) qq_28909_apart)
      (qq 30 28909) := by
  have divEq :
      RatEq
        (ratDivApart sigmaMinusOne (qq 28909 100) qq_28909_apart)
        (qq 30 28909) := by
    unfold sigmaMinusOne
    have leftCancel :
          RatEq
            (ratMul
              (ratDivApart (qq 3 10) (qq 28909 100) qq_28909_apart)
              (qq 28909 100))
            (qq 3 10) :=
        ratDivApart_mul_cancel_right qq_28909_apart
    have rightProduct :
          RatEq (ratMul (qq 30 28909) (qq 28909 100))
            (qq 3 10) := by
        exact RatEq_trans _ _ _
          (qq_mul (a := 30) (b := 28909) (c := 28909) (d := 100)
            (by decide) (by decide))
          (qq_eq_of_cross (by decide) (by decide) (by decide))
    exact BEDC.Real.RatNumLogEnclosure.ratMul_right_cancel_apart0
      (ratDivApart (qq 3 10) (qq 28909 100) qq_28909_apart)
      (qq 30 28909)
      (qq 28909 100)
      qq_28909_apart
      (RatEq_trans _ _ _ leftCancel (RatEq_symm rightProduct))
  exact divEq

theorem pole1_le (t : Rat) (ht : ratLe (natRat 17) t) :
    ratLe (pole1 t) (qq 130 29069) := by
  unfold pole1
  have denLe := pole1_baseline_den_le ht
  have divLe :
      ratLe
        (ratDivApart sigma
          (ratAdd (ratMul sigma sigma) (ratMul t t))
          (pole1_den_apart t))
        (ratDivApart sigma (qq 29069 100) qq_29069_apart) :=
    ratDivApart_le_same_num_den_mono
      sigma_nonneg qq_29069_pos (pole1_den_pos t)
      qq_29069_apart (pole1_den_apart t) denLe
  exact ratLe_of_RatEq_right divLe sigma_over_baseline_eq

theorem pole2_le (t : Rat) (ht : ratLe (natRat 17) t) :
    ratLe (pole2 t) (qq 30 28909) := by
  unfold pole2
  have denLe := pole2_baseline_den_le ht
  have divLe :
      ratLe
        (ratDivApart sigmaMinusOne
          (ratAdd (ratMul sigmaMinusOne sigmaMinusOne) (ratMul t t))
          (pole2_den_apart t))
        (ratDivApart sigmaMinusOne (qq 28909 100) qq_28909_apart) :=
    ratDivApart_le_same_num_den_mono
      sigmaMinusOne_nonneg qq_28909_pos (pole2_den_pos t)
      qq_28909_apart (pole2_den_apart t) denLe
  exact ratLe_of_RatEq_right divLe sigmaMinusOne_over_baseline_eq

def archA (t hRePsiVal hLogPiVal : Rat) : Rat :=
  ratSub (ratAdd (ratAdd (pole1 t) (pole2 t)) hRePsiVal) hLogPiVal

private theorem left_two_poles_eq :
    RatEq
      (ratAdd (qq 130 29069) (qq 30 28909))
      (qq 4630240 840355721) := by
  have h1 : RatEq (qq 130 29069) (qq 3758170 840355721) :=
    qq_eq_of_cross (by decide) (by decide) (by decide)
  have h2 : RatEq (qq 30 28909) (qq 872070 840355721) :=
    qq_eq_of_cross (by decide) (by decide) (by decide)
  exact RatEq_trans _ _ _
    (ratAdd_respects h1 h2)
    (qq_add_same_den (a := 3758170) (c := 872070)
      (m := 840355721) (by decide))

private theorem left_three_terms_eq :
    RatEq
      (ratAdd
        (ratAdd (qq 130 29069) (qq 30 28909))
        (qq 219685 200000))
      (qq 185539594567885 168071144200000) := by
  have h12 :
      RatEq
        (ratAdd (qq 130 29069) (qq 30 28909))
        (qq 926048000000 168071144200000) := by
    exact RatEq_trans _ _ _ left_two_poles_eq
      (qq_eq_of_cross (by decide) (by decide) (by decide))
  have h3 :
      RatEq (qq 219685 200000)
        (qq 184613546567885 168071144200000) :=
    qq_eq_of_cross (by decide) (by decide) (by decide)
  exact RatEq_trans _ _ _
    (ratAdd_respects h12 h3)
    (qq_add_same_den (a := 926048000000)
      (c := 184613546567885)
      (m := 168071144200000) (by decide))

private theorem right_terms_eq :
    RatEq
      (ratAdd (qq 531575 1000000) (qq 1144729 2000000))
      (qq 2207879 2000000) := by
  have h1 : RatEq (qq 531575 1000000) (qq 1063150 2000000) :=
    qq_eq_of_cross (by decide) (by decide) (by decide)
  exact RatEq_trans _ _ _
    (ratAdd_respects h1 (RatEq_refl _))
    (qq_add_same_den (a := 1063150) (c := 1144729)
      (m := 2000000) (by decide))

theorem arch_chain_le :
    ratLe
      (ratAdd
        (ratAdd (qq 130 29069) (qq 30 28909))
        (qq 219685 200000))
      (ratAdd (qq 531575 1000000) (qq 1144729 2000000)) := by
  have core :
      ratLe
        (qq 185539594567885 168071144200000)
        (qq 2207879 2000000) :=
    qq_crossLe (by decide) (by decide) (by decide)
  exact ratLe_congr left_three_terms_eq right_terms_eq core

private theorem arch_bound_plus_log_eq :
    RatEq
      (ratAdd (qq 531575 1000000) (qq 1144729 2000000))
      (ratAdd (qq 531575 1000000) (qq 1144729 2000000)) :=
  RatEq_refl _

theorem archA_le
    (t hRePsiVal hLogPiVal : Rat)
    (ht17 : ratLe (natRat 17) t)
    (hRePsi : ratLe hRePsiVal (qq 219685 200000))
    (hLogPi : ratLe (qq 1144729 2000000) hLogPiVal) :
    ratLe (archA t hRePsiVal hLogPiVal) (qq 531575 1000000) := by
  unfold archA
  have poleSum :
      ratLe
        (ratAdd (ratAdd (pole1 t) (pole2 t)) hRePsiVal)
        (ratAdd
          (ratAdd (qq 130 29069) (qq 30 28909))
          (qq 219685 200000)) :=
    ratAdd_le_add
      (ratAdd_le_add (pole1_le t ht17) (pole2_le t ht17))
      hRePsi
  have upper :
      ratLe
        (ratAdd (ratAdd (pole1 t) (pole2 t)) hRePsiVal)
        (ratAdd (qq 531575 1000000) (qq 1144729 2000000)) :=
    ratLe_trans poleSum arch_chain_le
  have subLe :
      ratLe
        (ratSub (ratAdd (ratAdd (pole1 t) (pole2 t)) hRePsiVal) hLogPiVal)
        (ratSub
          (ratAdd (qq 531575 1000000) (qq 1144729 2000000))
          (qq 1144729 2000000)) :=
    ratSub_le_sub_of_le_of_le upper hLogPi
  have cancel :
      RatEq
        (ratSub
          (ratAdd (qq 531575 1000000) (qq 1144729 2000000))
          (qq 1144729 2000000))
        (qq 531575 1000000) :=
    ratSub_eq_of_add_right_eq (RatEq_refl _)
  exact ratLe_of_RatEq_right subLe cancel

private theorem A_hi_eq :
    RatEq (qq 531575 1000000) StripExclusionAssembly.A_hi := by
  unfold StripExclusionAssembly.A_hi
  exact qq_eq_of_cross (by decide) (by decide) (by decide)

theorem archA_le_A_hi
    (t hRePsiVal hLogPiVal : Rat)
    (ht17 : ratLe (natRat 17) t)
    (hRePsi : ratLe hRePsiVal (qq 219685 200000))
    (hLogPi : ratLe (qq 1144729 2000000) hLogPiVal) :
    ratLe (archA t hRePsiVal hLogPiVal) StripExclusionAssembly.A_hi :=
  ratLe_of_RatEq_right
    (archA_le t hRePsiVal hLogPiVal ht17 hRePsi hLogPi)
    A_hi_eq

end BEDC.Derived.RHRoute.StripArchimedeanBound
