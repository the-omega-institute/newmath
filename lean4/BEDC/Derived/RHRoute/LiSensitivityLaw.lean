import BEDC.Derived.RHRoute.LiPhaseGeometry

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.LiSensitivityLaw

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.LiPhaseGeometry (natRat threeQuarterRat)
open BEDC.Derived.RHRoute.IntervalMatrixPSD (ratRingCanonical)

abbrev Rat : Type :=
  RatNum

def defect (σ γ : Rat) : Rat :=
  ratSub
    (ratAdd
      (ratMul (ratSub σ ratOne) (ratSub σ ratOne))
      (ratMul γ γ))
    (ratAdd (ratMul σ σ) (ratMul γ γ))

private theorem natRat_two_eq_one_add_one :
    RatEq (natRat 2) (ratAdd ratOne ratOne) := by
  have addNat :
      RatEq (ratAdd (natRat 1) (natRat 1)) (natRat 2) := by
    unfold natRat
    exact BEDC.Real.RatNumLogEnclosure.ratNat_add 1 1
  have oneNat :
      RatEq (natRat 1) ratOne := by
    unfold natRat BEDC.Real.RatNumKernel.ratNat ratOne intToRat
      BEDC.Derived.RationalUp.intOne BEDC.Derived.RationalUp.intOfNat
    exact RatEq_refl _
  have oneAdd :
      RatEq (ratAdd ratOne ratOne) (ratAdd (natRat 1) (natRat 1)) :=
    ratAdd_respects (RatEq_symm oneNat) (RatEq_symm oneNat)
  exact RatEq_symm (RatEq_trans _ _ _ oneAdd addNat)

private theorem rel_add_right_neg_cancel
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x y : A) :
    r (R.add (R.add x y) (R.neg y)) x := by
  exact R.trans (R.add_assoc x y (R.neg y))
    (R.trans (R.add_congr (R.refl x) (R.add_neg y))
      (R.add_zero x))

private theorem rel_add_right_cancel
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) {x y c : A} :
    r (R.add x c) (R.add y c) -> r x y := by
  intro h
  have shifted :
      r (R.add (R.add x c) (R.neg c))
        (R.add (R.add y c) (R.neg c)) :=
    R.add_congr h (R.refl (R.neg c))
  exact R.trans (R.symm (rel_add_right_neg_cancel R x c))
    (R.trans shifted (rel_add_right_neg_cancel R y c))

private theorem rel_sub_add_cancel_right
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x y : A) :
    r (R.add (R.sub y x) x) y := by
  exact R.trans (R.add_congr (R.sub_eq_add_neg y x) (R.refl x))
    (R.trans (R.add_assoc y (R.neg x) x)
      (R.trans (R.add_congr (R.refl y) (R.neg_add x))
        (R.add_zero y)))

private theorem rel_neg_sub_add_left
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x y : A) :
    r (R.add (R.neg (R.sub x y)) x) y := by
  let a := R.sub x y
  have hax : r (R.add a y) x :=
    rel_sub_add_cancel_right R y x
  have shifted :
      r (R.add (R.neg a) x) (R.add (R.neg a) (R.add a y)) :=
    R.add_congr (R.refl (R.neg a)) (R.symm hax)
  have collapsed :
      r (R.add (R.neg a) (R.add a y)) y :=
    R.trans (R.symm (R.add_assoc (R.neg a) a y))
      (R.trans (R.add_congr (R.neg_add a) (R.refl y))
        (R.zero_add y))
  exact R.trans shifted collapsed

private theorem rel_add_right_comm
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x y z : A) :
    r (R.add (R.add x y) z) (R.add (R.add x z) y) := by
  exact R.trans (R.add_assoc x y z)
    (R.trans
      (R.add_congr (R.refl x) (R.add_comm y z))
      (R.symm (R.add_assoc x z y)))

private theorem rel_two_mul_eq_add_self
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x : A) :
    r (R.mul (R.add R.one R.one) x) (R.add x x) := by
  exact R.trans (R.right_distrib R.one R.one x)
    (R.add_congr (R.one_mul x) (R.one_mul x))

private theorem rel_square_sub_one_add_self
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x : A) :
    r
      (R.add
        (R.mul (R.sub x R.one) (R.sub x R.one))
        x)
      (R.add (R.mul x (R.sub x R.one)) R.one) := by
  let a := R.sub x R.one
  have expandSquare :
      r (R.mul a a)
        (R.add (R.mul x a) (R.mul (R.neg R.one) a)) :=
    R.trans (R.mul_congr (R.sub_eq_add_neg x R.one) (R.refl a))
      (R.right_distrib x (R.neg R.one) a)
  have negTerm :
      r (R.mul (R.neg R.one) a) (R.neg a) :=
    R.trans (R.neg_mul R.one a)
      (R.neg_congr (R.one_mul a))
  have negPlus :
      r (R.add (R.neg a) x) R.one :=
    rel_neg_sub_add_left R x R.one
  exact R.trans (R.add_congr expandSquare (R.refl x))
    (R.trans
      (R.add_congr
        (R.add_congr (R.refl (R.mul x a)) negTerm)
        (R.refl x))
      (R.trans (R.add_assoc (R.mul x a) (R.neg a) x)
        (R.add_congr (R.refl (R.mul x a)) negPlus)))

private theorem rel_mul_sub_one_add_self
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x : A) :
    r
      (R.add (R.mul x (R.sub x R.one)) x)
      (R.mul x x) := by
  let a := R.sub x R.one
  have xAsMulOne : r x (R.mul x R.one) :=
    R.symm (R.mul_one x)
  have toProductSum :
      r (R.add (R.mul x a) x)
        (R.add (R.mul x a) (R.mul x R.one)) :=
    R.add_congr (R.refl (R.mul x a)) xAsMulOne
  have collect :
      r (R.add (R.mul x a) (R.mul x R.one))
        (R.mul x (R.add a R.one)) :=
    R.symm (R.left_distrib x a R.one)
  have closeSub : r (R.add a R.one) x :=
    rel_sub_add_cancel_right R R.one x
  exact R.trans toProductSum
    (R.trans collect (R.mul_congr (R.refl x) closeSub))

private theorem rel_square_sub_one_add_two_mul
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x : A) :
    r
      (R.add
        (R.mul (R.sub x R.one) (R.sub x R.one))
        (R.mul (R.add R.one R.one) x))
      (R.add (R.mul x x) R.one) := by
  let a := R.sub x R.one
  have twoAsAdd :
      r (R.mul (R.add R.one R.one) x) (R.add x x) :=
    rel_two_mul_eq_add_self R x
  have toAddSelf :
      r (R.add (R.mul a a) (R.mul (R.add R.one R.one) x))
        (R.add (R.mul a a) (R.add x x)) :=
    R.add_congr (R.refl (R.mul a a)) twoAsAdd
  have reassoc :
      r (R.add (R.mul a a) (R.add x x))
        (R.add (R.add (R.mul a a) x) x) :=
    R.symm (R.add_assoc (R.mul a a) x x)
  have firstCollapse :
      r (R.add (R.add (R.mul a a) x) x)
        (R.add (R.add (R.mul x a) R.one) x) :=
    R.add_congr (rel_square_sub_one_add_self R x) (R.refl x)
  have moveOne :
      r (R.add (R.add (R.mul x a) R.one) x)
        (R.add (R.add (R.mul x a) x) R.one) :=
    rel_add_right_comm R (R.mul x a) R.one x
  have closeProduct :
      r (R.add (R.mul x a) x) (R.mul x x) :=
    rel_mul_sub_one_add_self R x
  exact R.trans toAddSelf
    (R.trans reassoc
      (R.trans firstCollapse
        (R.trans moveOne
          (R.add_congr closeProduct (R.refl R.one)))))

private theorem rel_sub_self_add_to_neg
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (a b : A) :
    r (R.sub a (R.add a b)) (R.neg b) := by
  let c := R.add a b
  have leftPlus :
      r (R.add (R.sub a c) c) a :=
    rel_sub_add_cancel_right R c a
  have rightPlus :
      r (R.add (R.neg b) c) a := by
    unfold c
    exact R.trans (R.add_congr (R.refl (R.neg b)) (R.add_comm a b))
      (R.trans (R.symm (R.add_assoc (R.neg b) b a))
        (R.trans (R.add_congr (R.neg_add b) (R.refl a))
          (R.zero_add a)))
  exact rel_add_right_cancel R
    (R.trans leftPlus (R.symm rightPlus))

private theorem rel_one_sub_two_mul_add_square
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x : A) :
    r
      (R.add
        (R.sub R.one (R.mul (R.add R.one R.one) x))
        (R.mul x x))
      (R.mul (R.sub x R.one) (R.sub x R.one)) := by
  let twoX := R.mul (R.add R.one R.one) x
  let lhs := R.add (R.sub R.one twoX) (R.mul x x)
  let rhs := R.mul (R.sub x R.one) (R.sub x R.one)
  have leftPlus :
      r (R.add lhs twoX) (R.add (R.mul x x) R.one) := by
    unfold lhs
    exact R.trans
      (rel_add_right_comm R (R.sub R.one twoX) (R.mul x x) twoX)
      (R.trans
        (R.add_congr (rel_sub_add_cancel_right R twoX R.one)
          (R.refl (R.mul x x)))
        (R.add_comm R.one (R.mul x x)))
  have rightPlus :
      r (R.add rhs twoX) (R.add (R.mul x x) R.one) := by
    unfold rhs twoX
    exact rel_square_sub_one_add_two_mul R x
  exact rel_add_right_cancel R
    (R.trans leftPlus (R.symm rightPlus))

private theorem rel_core_plus_radius_eq_left
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x y : A) :
    r
      (R.add
        (R.sub R.one (R.mul (R.add R.one R.one) x))
        (R.add (R.mul x x) (R.mul y y)))
      (R.add
        (R.mul (R.sub x R.one) (R.sub x R.one))
        (R.mul y y)) := by
  exact R.trans
    (R.symm
      (R.add_assoc
        (R.sub R.one (R.mul (R.add R.one R.one) x))
        (R.mul x x)
        (R.mul y y)))
    (R.add_congr (rel_one_sub_two_mul_add_square R x)
      (R.refl (R.mul y y)))

private theorem rel_defect_eq_one_sub_two_mul
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x y : A) :
    r
      (R.sub
        (R.add
          (R.mul (R.sub x R.one) (R.sub x R.one))
          (R.mul y y))
        (R.add (R.mul x x) (R.mul y y)))
      (R.sub R.one (R.mul (R.add R.one R.one) x)) := by
  let left :=
    R.add
      (R.mul (R.sub x R.one) (R.sub x R.one))
      (R.mul y y)
  let radius := R.add (R.mul x x) (R.mul y y)
  let core := R.sub R.one (R.mul (R.add R.one R.one) x)
  have leftPlus :
      r (R.add (R.sub left radius) radius) left :=
    rel_sub_add_cancel_right R radius left
  have rightPlus :
      r (R.add core radius) left := by
    unfold core radius left
    exact rel_core_plus_radius_eq_left R x y
  exact rel_add_right_cancel R
    (R.trans leftPlus (R.symm rightPlus))

private theorem rel_one_sub_two_mul_half_add
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (h d : A)
    (hcrit : r (R.mul (R.add R.one R.one) h) R.one) :
    r
      (R.sub R.one (R.mul (R.add R.one R.one) (R.add h d)))
      (R.neg (R.mul (R.add R.one R.one) d)) := by
  let two := R.add R.one R.one
  have denomEq :
      r (R.mul two (R.add h d)) (R.add R.one (R.mul two d)) :=
    R.trans (R.left_distrib two h d)
      (R.add_congr hcrit (R.refl (R.mul two d)))
  have subReplace :
      r
        (R.sub R.one (R.mul two (R.add h d)))
        (R.sub R.one (R.add R.one (R.mul two d))) :=
    R.add_congr (R.refl R.one) (R.neg_congr denomEq)
  exact R.trans subReplace
    (rel_sub_self_add_to_neg R R.one (R.mul two d))

private theorem ratSub_respects {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> RatEq (ratSub x y) (ratSub x' y') := by
  intro hx hy
  unfold ratSub
  exact ratAdd_respects hx (ratNeg_respects hy)

private theorem ratHalf_critical :
    RatEq (ratMul (natRat 2) ratHalf) ratOne :=
  (BEDC.Derived.RHRoute.LiPhaseGeometry.equidistant_iff_critical
    ratHalf ratOne).mp
    BEDC.Derived.RHRoute.LiPhaseGeometry.half_one_equidistant

private theorem natRat_two_pos :
    ratLt ratZero (natRat 2) := by
  unfold ratLt intLtUp BEDC.Derived.IntUp.intLt natRat
    BEDC.Real.RatNumKernel.ratNat ratZero intToRat
    BEDC.Derived.RationalUp.intOfNat
  decide

theorem defect_eq_one_sub_two_sigma (σ γ : Rat) :
    RatEq (defect σ γ) (ratSub ratOne (ratMul (natRat 2) σ)) := by
  have core :
      RatEq (defect σ γ)
        (ratSub ratOne (ratMul (ratAdd ratOne ratOne) σ)) := by
    unfold defect
    exact rel_defect_eq_one_sub_two_mul ratRingCanonical σ γ
  have toNat :
      RatEq
        (ratSub ratOne (ratMul (ratAdd ratOne ratOne) σ))
        (ratSub ratOne (ratMul (natRat 2) σ)) :=
    ratSub_respects (RatEq_refl ratOne)
      (ratMul_respects (RatEq_symm natRat_two_eq_one_add_one) (RatEq_refl σ))
  exact RatEq_trans _ _ _ core toNat

theorem defect_at_perturbation (δ γ : Rat) :
    RatEq (defect (ratAdd ratHalf δ) γ)
      (ratNeg (ratMul (natRat 2) δ)) := by
  have core :=
    defect_eq_one_sub_two_sigma (ratAdd ratHalf δ) γ
  have toAddTwo :
      RatEq
        (ratSub ratOne (ratMul (natRat 2) (ratAdd ratHalf δ)))
        (ratSub ratOne
          (ratMul (ratAdd ratOne ratOne) (ratAdd ratHalf δ))) :=
    ratSub_respects (RatEq_refl ratOne)
      (ratMul_respects natRat_two_eq_one_add_one
        (RatEq_refl (ratAdd ratHalf δ)))
  have halfCritAdd :
      RatEq (ratMul (ratAdd ratOne ratOne) ratHalf) ratOne :=
    RatEq_trans _ _ _
      (ratMul_respects (RatEq_symm natRat_two_eq_one_add_one)
        (RatEq_refl ratHalf))
      ratHalf_critical
  have perturb :
      RatEq
        (ratSub ratOne
          (ratMul (ratAdd ratOne ratOne) (ratAdd ratHalf δ)))
        (ratNeg (ratMul (ratAdd ratOne ratOne) δ)) :=
    rel_one_sub_two_mul_half_add ratRingCanonical ratHalf δ halfCritAdd
  have toNatNeg :
      RatEq (ratNeg (ratMul (ratAdd ratOne ratOne) δ))
        (ratNeg (ratMul (natRat 2) δ)) :=
    ratNeg_respects
      (ratMul_respects (RatEq_symm natRat_two_eq_one_add_one)
        (RatEq_refl δ))
  exact RatEq_trans _ _ _ core
    (RatEq_trans _ _ _ toAddTwo
      (RatEq_trans _ _ _ perturb toNatNeg))

theorem defect_pos_of_lt_half (σ γ : Rat) (h : ratLt σ ratHalf) :
    ratLt ratZero (defect σ γ) := by
  have scaled :
      ratLt (ratMul (natRat 2) σ) (ratMul (natRat 2) ratHalf) :=
    ratMul_lt_mul_left h natRat_two_pos
  have scaledOne :
      ratLt (ratMul (natRat 2) σ) ratOne :=
    BEDC.Real.RatNumKernel.ratLt_of_RatEq_right scaled ratHalf_critical
  have corePos :
      ratLt ratZero (ratSub ratOne (ratMul (natRat 2) σ)) :=
    sub_pos_of_lt scaledOne
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
    corePos
    (RatEq_symm (defect_eq_one_sub_two_sigma σ γ))

theorem defect_neg_of_gt_half (σ γ : Rat) (h : ratLt ratHalf σ) :
    ratLt (defect σ γ) ratZero := by
  have scaled :
      ratLt (ratMul (natRat 2) ratHalf) (ratMul (natRat 2) σ) :=
    ratMul_lt_mul_left h natRat_two_pos
  have oneScaled :
      ratLt ratOne (ratMul (natRat 2) σ) :=
    BEDC.Real.RatNumKernel.ratLt_of_RatEq_left
      (RatEq_symm ratHalf_critical)
      scaled
  have coreRaw :
      ratLt (ratSub ratOne (ratMul (natRat 2) σ))
        (ratSub ratOne ratOne) :=
    const_sub_strictAnti oneScaled
  have coreNeg :
      ratLt (ratSub ratOne (ratMul (natRat 2) σ)) ratZero :=
    BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
      coreRaw
      (ratSub_self ratOne)
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_left
    (defect_eq_one_sub_two_sigma σ γ)
    coreNeg

theorem defect_zero_of_critical (σ γ : Rat)
    (h : RatEq (ratMul (natRat 2) σ) ratOne) :
    RatEq (defect σ γ) ratZero := by
  have coreZero :
      RatEq (ratSub ratOne (ratMul (natRat 2) σ)) ratZero :=
    (ratSub_zero_iff ratOne (ratMul (natRat 2) σ)).mpr
      (RatEq_symm h)
  exact RatEq_trans _ _ _
    (defect_eq_one_sub_two_sigma σ γ)
    coreZero

def ratQuarter : Rat :=
  ratMul ratHalf ratHalf

theorem critical_denominator_eq (γ : Rat) :
    RatEq
      (ratAdd (ratMul ratHalf ratHalf) (ratMul γ γ))
      (ratAdd ratQuarter (ratMul γ γ)) := by
  unfold ratQuarter
  exact RatEq_refl _

private theorem threeQuarter_defect_core :
    RatEq (ratSub ratOne (ratMul (natRat 2) threeQuarterRat))
      (ratNeg ratHalf) := by
  unfold threeQuarterRat natRat BEDC.Real.RatNumKernel.ratNat ratSub ratMul
    ratAdd ratNeg ratOne ratHalf intToRat RatEq
    BEDC.Derived.RationalUp.intOfNat
  exact IntPairClassifier_of_length_eq (intToPair_carrier _)
    (intToPair_carrier _) (by decide)

theorem defect_three_quarter (γ : Rat) :
    RatEq (defect threeQuarterRat γ) (ratNeg ratHalf) := by
  exact RatEq_trans _ _ _
    (defect_eq_one_sub_two_sigma threeQuarterRat γ)
    threeQuarter_defect_core

private theorem oneQuarter_defect_core :
    RatEq (ratSub ratOne (ratMul (natRat 2) ratQuarter)) ratHalf := by
  unfold ratQuarter natRat BEDC.Real.RatNumKernel.ratNat ratSub ratMul
    ratAdd ratNeg ratOne ratHalf intToRat RatEq
    BEDC.Derived.RationalUp.intOfNat
  exact IntPairClassifier_of_length_eq (intToPair_carrier _)
    (intToPair_carrier _) (by decide)

theorem defect_one_quarter (γ : Rat) :
    RatEq (defect ratQuarter γ) ratHalf := by
  exact RatEq_trans _ _ _
    (defect_eq_one_sub_two_sigma ratQuarter γ)
    oneQuarter_defect_core

end BEDC.Derived.RHRoute.LiSensitivityLaw
