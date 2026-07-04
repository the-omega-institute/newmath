import BEDC.Derived.RHRoute.PrimeWindowDefect
import BEDC.Derived.RationalOrderArithUp
import BEDC.Real.RatNumKernel

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.BedcZetaCriticalUnit

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.PrimeWindowDefect

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  PrimeWindowDefect.RatComplex

abbrev NontrivialZetaZero :=
  PrimeWindowDefect.NontrivialZetaZero

abbrev ConstructiveRH :=
  PrimeWindowDefect.ConstructiveRH

def radialEnergy (r len : Rat) : Rat :=
  ratMul (ratMul r r) len

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    IntEq (IntMul (IntMul x.num intZero) (ratDenInt ratZero))
      (IntMul intZero (ratDenInt (ratMul x ratZero)))
  exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
    (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))

private theorem ratMul_zero_left_local (x : Rat) :
    RatEq (ratMul ratZero x) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm ratZero x) (ratMul_zero_right_local x)

private theorem ratMul_neg_right_local (x y : Rat) :
    RatEq (ratMul x (ratNeg y)) (ratNeg (ratMul x y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratMul ratNeg
    exact BEDC.Algebra.Rel.IntegerUp_mul_neg x.num y.num
  · unfold ratMul ratNeg ratDenInt
    exact IntEq_refl _

private theorem ratMul_neg_left_local (x y : Rat) :
    RatEq (ratMul (ratNeg x) y) (ratNeg (ratMul x y)) := by
  exact RatEq_trans _ _ _
    (ratMul_comm (ratNeg x) y)
    (RatEq_trans _ _ _
      (ratMul_neg_right_local y x)
      (ratNeg_respects (ratMul_comm y x)))

private theorem ratNeg_mul_neg_local (x y : Rat) :
    RatEq (ratMul (ratNeg x) (ratNeg y)) (ratMul x y) := by
  exact RatEq_trans _ _ _
    (ratMul_neg_left_local x (ratNeg y))
    (RatEq_trans _ _ _
      (ratNeg_respects (ratMul_neg_right_local x y))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local (ratMul x y)))

private theorem ratNeg_pos_of_neg_local {x : Rat} :
    ratLt x ratZero -> ratLt ratZero (ratNeg x) := by
  intro h
  have subPos : ratLt ratZero (ratSub ratZero x) :=
    sub_pos_of_lt h
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
    subPos
    (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x)

private theorem ratMul_pos_local {x y : Rat} :
    ratLt ratZero x -> ratLt ratZero y -> ratLt ratZero (ratMul x y) := by
  intro hx hy
  have raw : ratLt (ratMul ratZero y) (ratMul x y) :=
    ratMul_lt_mul_right hx hy
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_left
    (RatEq_symm (ratMul_zero_left_local y)) raw

private theorem ratMul_self_nonneg_local (x : Rat) :
    ratLe ratZero (ratMul x x) := by
  cases rat_order_trichotomy ratZero x with
  | inl xPos =>
      exact BEDC.Real.RatNumKernel.ratMul_nonneg
        (ratLt_to_ratLe xPos) (ratLt_to_ratLe xPos)
  | inr rest =>
      cases rest with
      | inl xZero =>
          have squareZero : RatEq (ratMul x x) ratZero :=
            RatEq_trans _ _ _
              (ratMul_respects (RatEq_symm xZero) (RatEq_symm xZero))
              (ratMul_zero_left_local ratZero)
          exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
            (ratLe_refl ratZero) (RatEq_symm squareZero)
      | inr xNeg =>
          have negNonneg : ratLe ratZero (ratNeg x) :=
            ratLt_to_ratLe (ratNeg_pos_of_neg_local xNeg)
          have negSquareNonneg :
              ratLe ratZero (ratMul (ratNeg x) (ratNeg x)) :=
            BEDC.Real.RatNumKernel.ratMul_nonneg negNonneg negNonneg
          exact BEDC.Real.RatNumKernel.ratLe_of_RatEq_right
            negSquareNonneg (ratNeg_mul_neg_local x x)

private theorem rat_square_eq_zero_forces_zero_local (r : Rat) :
    RatEq (ratMul r r) ratZero -> RatEq r ratZero := by
  intro hSquare
  cases rat_order_trichotomy ratZero r with
  | inl rPos =>
      have squarePos : ratLt ratZero (ratMul r r) :=
        ratMul_pos_local rPos rPos
      exact False.elim
        (ratLt_not_RatEq squarePos (RatEq_symm hSquare))
  | inr rest =>
      cases rest with
      | inl rZero =>
          exact RatEq_symm rZero
      | inr rNeg =>
          have negPos : ratLt ratZero (ratNeg r) :=
            ratNeg_pos_of_neg_local rNeg
          have negSquarePos :
              ratLt ratZero (ratMul (ratNeg r) (ratNeg r)) :=
            ratMul_pos_local negPos negPos
          have squarePos : ratLt ratZero (ratMul r r) :=
            BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
              negSquarePos
              (ratNeg_mul_neg_local r r)
          exact False.elim
            (ratLt_not_RatEq squarePos (RatEq_symm hSquare))

theorem radialEnergy_zero_of_zero (len : Rat) :
    RatEq (radialEnergy ratZero len) ratZero := by
  unfold radialEnergy
  exact RatEq_trans _ _ _
    (ratMul_respects (ratMul_zero_left_local ratZero) (RatEq_refl len))
    (ratMul_zero_left_local len)

theorem radialEnergy_pos_of_ne
    (r len : Rat) (hr : ratApart0 r) (hlen : ratLt ratZero len) :
    ratLt ratZero (radialEnergy r len) := by
  unfold radialEnergy
  have sqPos : ratLt ratZero (ratMul r r) := by
    cases rat_order_trichotomy ratZero r with
    | inl rPos =>
        exact ratMul_pos_local rPos rPos
    | inr rest =>
        cases rest with
        | inl rZero =>
            exact False.elim
              (intApart0_not_zero_pair hr
                (RatEq_zero_num (RatEq_symm rZero)))
        | inr rNeg =>
            have negPos : ratLt ratZero (ratNeg r) :=
              ratNeg_pos_of_neg_local rNeg
            have negSqPos :
                ratLt ratZero (ratMul (ratNeg r) (ratNeg r)) :=
              ratMul_pos_local negPos negPos
            exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
              negSqPos
              (ratNeg_mul_neg_local r r)
  exact ratMul_pos_local sqPos hlen

theorem radialEnergy_not_zero_of_ne
    (r len : Rat) (hr : ratApart0 r) (hlen : ratLt ratZero len) :
    RatEq (radialEnergy r len) ratZero -> False := by
  intro hzero
  exact ratLt_not_RatEq
    (radialEnergy_pos_of_ne r len hr hlen)
    (RatEq_symm hzero)

theorem radialEnergy_zero_iff (r len : Rat)
    (hlen : ratLt ratZero len) :
    RatEq (radialEnergy r len) ratZero ↔ RatEq r ratZero := by
  constructor
  · intro hEnergy
    have sqNonneg : ratLe ratZero (ratMul r r) :=
      ratMul_self_nonneg_local r
    have productZero :
        RatEq (ratMul (ratMul r r) len) ratZero := by
      exact hEnergy
    have sqZero : RatEq (ratMul r r) ratZero := by
      cases rat_order_trichotomy ratZero (ratMul r r) with
      | inl sqPos =>
          have productPos :
              ratLt ratZero (ratMul (ratMul r r) len) :=
            ratMul_pos_local sqPos hlen
          exact False.elim
            (ratLt_not_RatEq productPos (RatEq_symm productZero))
      | inr rest =>
          cases rest with
          | inl sqEqZero =>
              exact RatEq_symm sqEqZero
          | inr sqNeg =>
              exact False.elim
                (ratLt_not_ratLe_reverse sqNeg sqNonneg)
    exact rat_square_eq_zero_forces_zero_local r sqZero
  · intro hZero
    unfold radialEnergy
    have squareZero : RatEq (ratMul r r) ratZero :=
      RatEq_trans _ _ _
        (ratMul_respects hZero hZero)
        (ratMul_zero_left_local ratZero)
    exact RatEq_trans _ _ _
      (ratMul_respects squareZero (RatEq_refl len))
      (ratMul_zero_left_local len)

def offsetOf (s : RatComplex) : Rat :=
  ratSub s.re BEDC.Derived.RHRoute.BoxKernelConcrete.halfRat

-- This proposition is RH-strength: it names the single deferred hinge
-- asserting that legal closed zeta-zero residuals have unit radial modulus.
def CriticalUnitSoundness : Prop :=
  ∀ s : RatComplex, NontrivialZetaZero s -> RatEq (offsetOf s) ratZero

structure ZetaBEDCClosure where
  criticalUnitSoundness : CriticalUnitSoundness

theorem offset_zero_of_energy_zero
    (s : RatComplex) (len : Rat) (hlen : ratLt ratZero len)
    (h : RatEq (radialEnergy (offsetOf s) len) ratZero) :
    RatEq (offsetOf s) ratZero :=
  (radialEnergy_zero_iff (offsetOf s) len hlen).mp h

theorem zetaBEDC_closure_imply_constructiveRH
    (Z : ZetaBEDCClosure) :
    ConstructiveRH := by
  intro s hs
  have hOffset : RatEq (offsetOf s) ratZero :=
    Z.criticalUnitSoundness s hs
  unfold offsetOf at hOffset
  change RatEq s.re BEDC.Derived.RHRoute.BoxKernelConcrete.halfRat
  exact (ratSub_zero_iff s.re
    BEDC.Derived.RHRoute.BoxKernelConcrete.halfRat).mp hOffset

end BEDC.Derived.RHRoute.BedcZetaCriticalUnit
