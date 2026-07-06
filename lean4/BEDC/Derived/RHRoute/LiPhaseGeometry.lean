import BEDC.Derived.RHRoute.IntervalMatrixPSD.RatRingCanonical
import BEDC.Derived.RHRoute.JensenTuranDegree2

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RHRoute.LiPhaseGeometry

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RHRoute.IntervalMatrixPSD (ratRingCanonical)

abbrev Rat : Type :=
  RatNum

def natRat (n : Nat) : Rat :=
  BEDC.Real.RatNumKernel.ratNat n

private theorem natRat_add (m n : Nat) :
    RatEq (ratAdd (natRat m) (natRat n)) (natRat (m + n)) := by
  unfold natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_add m n

private theorem natRat_mul (m n : Nat) :
    RatEq (ratMul (natRat m) (natRat n)) (natRat (m * n)) := by
  unfold natRat
  exact BEDC.Real.RatNumLogEnclosure.ratNat_mul m n

private theorem natRat_one_eq :
    RatEq (natRat 1) ratOne := by
  unfold natRat BEDC.Real.RatNumKernel.ratNat ratOne intToRat
    BEDC.Derived.RationalUp.intOne BEDC.Derived.RationalUp.intOfNat
  exact RatEq_refl _

private theorem natRat_two_eq_one_add_one :
    RatEq (natRat 2) (ratAdd ratOne ratOne) := by
  have addNat :
      RatEq (ratAdd (natRat 1) (natRat 1)) (natRat 2) :=
    natRat_add 1 1
  have oneAdd :
      RatEq (ratAdd ratOne ratOne) (ratAdd (natRat 1) (natRat 1)) :=
    ratAdd_respects (RatEq_symm natRat_one_eq) (RatEq_symm natRat_one_eq)
  exact RatEq_symm (RatEq_trans _ _ _ oneAdd addNat)

private theorem ratMul_zero_right_local (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  unfold RatEq ratMul ratZero intToRat
  change
    BEDC.Derived.RationalUp.IntEq
      (BEDC.Derived.RationalUp.IntMul
        (BEDC.Derived.RationalUp.IntMul x.num BEDC.Derived.RationalUp.intZero)
        (ratDenInt ratZero))
      (BEDC.Derived.RationalUp.IntMul BEDC.Derived.RationalUp.intZero
        (ratDenInt (ratMul x ratZero)))
  exact IntEq_trans (intMul_right_congr (intMul_zero_right x.num))
    (IntEq_symm (intMul_zero_left (ratDenInt (ratMul x ratZero))))

private theorem ratMul_zero_left_local (x : Rat) :
    RatEq (ratMul ratZero x) ratZero :=
  RatEq_trans _ _ _ (ratMul_comm ratZero x) (ratMul_zero_right_local x)

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

private theorem rel_add_left_cancel
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) {x y c : A} :
    r (R.add c x) (R.add c y) -> r x y := by
  intro h
  apply rel_add_right_cancel R (c := c)
  exact R.trans (R.add_comm x c)
    (R.trans h (R.add_comm c y))

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

private theorem rel_sub_add_sub_cancel
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x y : A) :
    r (R.add (R.sub x y) (R.sub y x)) R.zero := by
  have expand :
      r (R.add (R.sub x y) (R.sub y x))
        (R.add (R.add x (R.neg y)) (R.add y (R.neg x))) :=
    R.add_congr (R.sub_eq_add_neg x y) (R.sub_eq_add_neg y x)
  have reassoc :
      r (R.add (R.add x (R.neg y)) (R.add y (R.neg x)))
        (R.add x (R.add (R.neg y) (R.add y (R.neg x)))) :=
    R.add_assoc x (R.neg y) (R.add y (R.neg x))
  have inner :
      r (R.add (R.neg y) (R.add y (R.neg x))) (R.neg x) :=
    R.trans (R.symm (R.add_assoc (R.neg y) y (R.neg x)))
      (R.trans (R.add_congr (R.neg_add y) (R.refl (R.neg x)))
        (R.zero_add (R.neg x)))
  exact R.trans expand
    (R.trans reassoc
      (R.trans (R.add_congr (R.refl x) inner)
        (R.add_neg x)))

private theorem rel_sub_swap_neg
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x y : A) :
    r (R.sub x y) (R.neg (R.sub y x)) := by
  have sumZero :
      r (R.add (R.sub y x) (R.sub x y)) R.zero :=
    rel_sub_add_sub_cancel R y x
  exact R.eq_neg_of_add_eq_zero
    (a := R.sub y x) (b := R.sub x y) sumZero

private theorem rel_sub_square_symm
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x y : A) :
    r (R.mul (R.sub x y) (R.sub x y))
      (R.mul (R.sub y x) (R.sub y x)) := by
  exact R.trans
    (R.mul_congr (rel_sub_swap_neg R x y) (rel_sub_swap_neg R x y))
    (R.neg_neg_mul_neg (R.sub y x) (R.sub y x))

private theorem rel_li_left_plus_two_mul
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (c : A) :
    r
      (R.add
        (R.mul (R.add R.one R.one) (R.sub R.one c))
        (R.mul (R.add R.one R.one) c))
      (R.add R.one R.one) := by
  let two := R.add R.one R.one
  have collect :
      r (R.add (R.mul two (R.sub R.one c)) (R.mul two c))
        (R.mul two (R.add (R.sub R.one c) c)) :=
    R.symm (R.left_distrib two (R.sub R.one c) c)
  have closeSub :
      r (R.add (R.sub R.one c) c) R.one :=
    rel_sub_add_cancel_right R c R.one
  exact R.trans collect
    (R.trans (R.mul_congr (R.refl two) closeSub)
      (R.mul_one two))

private theorem rel_li_sos_plus_two_mul
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (c s : A)
    (hcs : r (R.add (R.mul c c) (R.mul s s)) R.one) :
    r
      (R.add
        (R.add
          (R.mul (R.sub R.one c) (R.sub R.one c))
          (R.mul s s))
        (R.mul (R.add R.one R.one) c))
      (R.add R.one R.one) := by
  let oneMinus := R.sub R.one c
  let cMinus := R.sub c R.one
  let twoC := R.mul (R.add R.one R.one) c
  have moveTwoC :
      r
        (R.add (R.add (R.mul oneMinus oneMinus) (R.mul s s)) twoC)
        (R.add (R.add (R.mul oneMinus oneMinus) twoC) (R.mul s s)) :=
    rel_add_right_comm R (R.mul oneMinus oneMinus) (R.mul s s) twoC
  have squareSymm :
      r (R.mul oneMinus oneMinus) (R.mul cMinus cMinus) :=
    rel_sub_square_symm R R.one c
  have replaceSquare :
      r
        (R.add (R.add (R.mul oneMinus oneMinus) twoC) (R.mul s s))
        (R.add (R.add (R.mul cMinus cMinus) twoC) (R.mul s s)) :=
    R.add_congr
      (R.add_congr squareSymm (R.refl twoC))
      (R.refl (R.mul s s))
  have squareLine :
      r (R.add (R.mul cMinus cMinus) twoC)
        (R.add (R.mul c c) R.one) :=
    rel_square_sub_one_add_two_mul R c
  have replaceLine :
      r
        (R.add (R.add (R.mul cMinus cMinus) twoC) (R.mul s s))
        (R.add (R.add (R.mul c c) R.one) (R.mul s s)) :=
    R.add_congr squareLine (R.refl (R.mul s s))
  have moveUnit :
      r
        (R.add (R.add (R.mul c c) R.one) (R.mul s s))
        (R.add (R.add (R.mul c c) (R.mul s s)) R.one) :=
    rel_add_right_comm R (R.mul c c) R.one (R.mul s s)
  have unitFirst :
      r
        (R.add (R.add (R.mul c c) (R.mul s s)) R.one)
        (R.add R.one (R.add (R.mul c c) (R.mul s s))) :=
    R.add_comm (R.add (R.mul c c) (R.mul s s)) R.one
  exact R.trans moveTwoC
    (R.trans replaceSquare
      (R.trans replaceLine
        (R.trans moveUnit
          (R.trans unitFirst
            (R.add_congr (R.refl R.one) hcs)))))

private theorem rel_li_online_sos_identity
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (c s : A)
    (hcs : r (R.add (R.mul c c) (R.mul s s)) R.one) :
    r
      (R.mul (R.add R.one R.one) (R.sub R.one c))
      (R.add
        (R.mul (R.sub R.one c) (R.sub R.one c))
        (R.mul s s)) := by
  let rhs :=
    R.add
      (R.mul (R.sub R.one c) (R.sub R.one c))
      (R.mul s s)
  let twoC := R.mul (R.add R.one R.one) c
  have leftPlus :
      r (R.add (R.mul (R.add R.one R.one) (R.sub R.one c)) twoC)
        (R.add R.one R.one) :=
    rel_li_left_plus_two_mul R c
  have rightPlus :
      r (R.add rhs twoC) (R.add R.one R.one) :=
    rel_li_sos_plus_two_mul R c s hcs
  have sameAfter :
      r (R.add (R.mul (R.add R.one R.one) (R.sub R.one c)) twoC)
        (R.add rhs twoC) :=
    R.trans leftPlus (R.symm rightPlus)
  exact rel_add_right_cancel R sameAfter

private theorem rel_equidistant_iff_critical
    {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x y : A) :
    (r
      (R.add
        (R.mul (R.sub x R.one) (R.sub x R.one))
        (R.mul y y))
      (R.add (R.mul x x) (R.mul y y))) ↔
    r (R.mul (R.add R.one R.one) x) R.one := by
  constructor
  · intro h
    have squareEq :
        r (R.mul (R.sub x R.one) (R.sub x R.one)) (R.mul x x) :=
      rel_add_right_cancel R h
    have shifted :
        r
          (R.add
            (R.mul (R.sub x R.one) (R.sub x R.one))
            (R.mul (R.add R.one R.one) x))
          (R.add (R.mul x x) (R.mul (R.add R.one R.one) x)) :=
      R.add_congr squareEq (R.refl (R.mul (R.add R.one R.one) x))
    have lineId :
        r
          (R.add (R.mul x x) R.one)
          (R.add (R.mul x x) (R.mul (R.add R.one R.one) x)) :=
      R.trans (R.symm (rel_square_sub_one_add_two_mul R x)) shifted
    have oneEq :
        r R.one (R.mul (R.add R.one R.one) x) :=
      rel_add_left_cancel R lineId
    exact R.symm oneEq
  · intro h
    have shifted :
        r
          (R.add
            (R.mul (R.sub x R.one) (R.sub x R.one))
            (R.mul (R.add R.one R.one) x))
          (R.add (R.mul x x) (R.mul (R.add R.one R.one) x)) :=
      R.trans (rel_square_sub_one_add_two_mul R x)
        (R.add_congr (R.refl (R.mul x x)) (R.symm h))
    have squareEq :
        r (R.mul (R.sub x R.one) (R.sub x R.one)) (R.mul x x) :=
      rel_add_right_cancel R shifted
    exact R.add_congr squareEq (R.refl (R.mul y y))

theorem equidistant_iff_critical (σ γ : Rat) :
    RatEq
      (ratAdd
        (ratMul (ratSub σ ratOne) (ratSub σ ratOne))
        (ratMul γ γ))
      (ratAdd (ratMul σ σ) (ratMul γ γ)) ↔
    RatEq (ratMul (natRat 2) σ) ratOne := by
  have core :
      RatEq
        (ratAdd
          (ratMul (ratSub σ ratOne) (ratSub σ ratOne))
          (ratMul γ γ))
        (ratAdd (ratMul σ σ) (ratMul γ γ)) ↔
      RatEq (ratMul (ratAdd ratOne ratOne) σ) ratOne :=
    rel_equidistant_iff_critical ratRingCanonical σ γ
  constructor
  · intro h
    exact RatEq_trans _ _ _
      (ratMul_respects natRat_two_eq_one_add_one (RatEq_refl σ))
      (core.mp h)
  · intro h
    apply core.mpr
    exact RatEq_trans _ _ _
      (ratMul_respects (RatEq_symm natRat_two_eq_one_add_one) (RatEq_refl σ))
      h

theorem li_online_sos_identity (c s : Rat)
    (hcs : RatEq (ratAdd (ratMul c c) (ratMul s s)) ratOne) :
    RatEq
      (ratMul (natRat 2) (ratSub ratOne c))
      (ratAdd
        (ratMul (ratSub ratOne c) (ratSub ratOne c))
        (ratMul s s)) := by
  exact RatEq_trans _ _ _
    (ratMul_respects natRat_two_eq_one_add_one
      (RatEq_refl (ratSub ratOne c)))
    (rel_li_online_sos_identity ratRingCanonical c s hcs)

private theorem ratAdd_nonneg_local {x y : Rat} :
    ratLe ratZero x -> ratLe ratZero y -> ratLe ratZero (ratAdd x y) := by
  intro hx hy
  have raw :
      ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    BEDC.Real.RatNumKernel.ratAdd_le_add hx hy
  exact ratLe_respects (ratZero_add_left ratZero) (RatEq_refl _) raw

theorem li_online_nonneg (c s : Rat) :
    ratLe ratZero
      (ratAdd
        (ratMul (ratSub ratOne c) (ratSub ratOne c))
        (ratMul s s)) := by
  exact ratAdd_nonneg_local
    (BEDC.Derived.RHRoute.JensenTuranDegree2.ratMul_self_nonneg
      (ratSub ratOne c))
    (BEDC.Derived.RHRoute.JensenTuranDegree2.ratMul_self_nonneg s)

theorem li_online_contribution_nonneg (c s : Rat)
    (hcs : RatEq (ratAdd (ratMul c c) (ratMul s s)) ratOne) :
    ratLe ratZero (ratMul (natRat 2) (ratSub ratOne c)) := by
  exact ratLe_respects (RatEq_refl ratZero)
    (RatEq_symm (li_online_sos_identity c s hcs))
    (li_online_nonneg c s)

private theorem ratHalf_add_half_eq_one :
    RatEq (ratAdd ratHalf ratHalf) ratOne := by
  unfold ratHalf ratOne intToRat ratAdd RatEq
    BEDC.Derived.RationalUp.intOfNat BEDC.Derived.RationalUp.intOne
  exact IntPairClassifier_of_length_eq (intToPair_carrier _)
    (intToPair_carrier _) (by decide)

private theorem ratHalf_critical :
    RatEq (ratMul (natRat 2) ratHalf) ratOne := by
  exact RatEq_trans _ _ _
    (ratMul_respects natRat_two_eq_one_add_one (RatEq_refl ratHalf))
    (RatEq_trans _ _ _
      (rel_two_mul_eq_add_self ratRingCanonical ratHalf)
      ratHalf_add_half_eq_one)

theorem half_one_equidistant :
    RatEq
      (ratAdd
        (ratMul (ratSub ratHalf ratOne) (ratSub ratHalf ratOne))
        (ratMul ratOne ratOne))
      (ratAdd (ratMul ratHalf ratHalf) (ratMul ratOne ratOne)) :=
  (equidistant_iff_critical ratHalf ratOne).mpr ratHalf_critical

private theorem natToUnary_four_den_pos :
    BEDC.Derived.NatUp.NatUnaryStrictPrefix BEDC.Derived.PadicUp.NatOne
        (BEDC.Derived.IntUp.natToUnary 4) ∨
      hsame (BEDC.Derived.IntUp.natToUnary 4) BEDC.Derived.PadicUp.NatOne := by
  apply Or.inl
  apply BEDC.Derived.PadicUp.NatUnaryStrictPrefix_of_length_lt
  · exact unary_e1_closed unary_empty
  · exact BEDC.Derived.IntUp.natToUnary_unary 4
  · change
      bwordLength BEDC.Derived.PadicUp.NatOne <
        bwordLength (BEDC.Derived.IntUp.natToUnary 4)
    rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.right.left
      BHist.Empty unary_empty]
    rw [BEDC.Derived.IntUp.natToUnary_length]
    decide

def threeQuarterRat : Rat :=
  { num :=
      BEDC.Derived.RationalUp.intOfNat (BEDC.Derived.IntUp.natToUnary 3)
        (BEDC.Derived.IntUp.natToUnary_unary 3)
    den := BEDC.Derived.IntUp.natToUnary 4
    den_pos := natToUnary_four_den_pos }

theorem three_quarters_not_critical :
    RatEq (ratMul (natRat 2) threeQuarterRat) ratOne -> False := by
  intro h
  unfold threeQuarterRat natRat BEDC.Real.RatNumKernel.ratNat ratMul ratOne
    intToRat RatEq BEDC.Derived.RationalUp.intOfNat at h
  change
    BEDC.Derived.IntUp.IntPairClassifier
      (BEDC.Derived.IntUp.natToUnary 6, BHist.Empty)
      (BEDC.Derived.IntUp.natToUnary 4, BHist.Empty) at h
  have same := h.right.right
  change hsame (BEDC.Derived.IntUp.natToUnary 6)
    (BEDC.Derived.IntUp.natToUnary 4) at same
  cases same

theorem three_quarters_one_not_equidistant :
    RatEq
      (ratAdd
        (ratMul (ratSub threeQuarterRat ratOne) (ratSub threeQuarterRat ratOne))
        (ratMul ratOne ratOne))
      (ratAdd (ratMul threeQuarterRat threeQuarterRat) (ratMul ratOne ratOne)) ->
    False := by
  intro h
  exact three_quarters_not_critical
    ((equidistant_iff_critical threeQuarterRat ratOne).mp h)

private theorem cos_one_sin_zero_unit :
    RatEq
      (ratAdd (ratMul ratOne ratOne) (ratMul ratZero ratZero))
      ratOne := by
  exact RatEq_trans _ _ _
    (ratAdd_respects (ratMul_one_right ratOne)
      (ratMul_zero_left_local ratZero))
    (ratAdd_zero_right ratOne)

private theorem cos_neg_one_sin_zero_unit :
    RatEq
      (ratAdd
        (ratMul (ratNeg ratOne) (ratNeg ratOne))
        (ratMul ratZero ratZero))
      ratOne := by
  exact RatEq_trans _ _ _
    (ratAdd_respects
      (RatEq_trans _ _ _
        (ratRingCanonical.neg_neg_mul_neg ratOne ratOne)
        (ratMul_one_right ratOne))
      (ratMul_zero_left_local ratZero))
    (ratAdd_zero_right ratOne)

theorem li_online_zero_angle_identity :
    RatEq
      (ratMul (natRat 2) (ratSub ratOne ratOne))
      (ratAdd
        (ratMul (ratSub ratOne ratOne) (ratSub ratOne ratOne))
        (ratMul ratZero ratZero)) :=
  li_online_sos_identity ratOne ratZero cos_one_sin_zero_unit

theorem li_online_zero_angle_zero :
    RatEq (ratMul (natRat 2) (ratSub ratOne ratOne)) ratZero := by
  have subZero :
      RatEq (ratSub ratOne ratOne) ratZero :=
    (ratSub_zero_iff ratOne ratOne).mpr (RatEq_refl ratOne)
  exact RatEq_trans _ _ _
    (ratMul_respects (RatEq_refl (natRat 2)) subZero)
    (ratMul_zero_right_local (natRat 2))

theorem li_online_zero_angle_sos_zero :
    RatEq
      (ratAdd
        (ratMul (ratSub ratOne ratOne) (ratSub ratOne ratOne))
        (ratMul ratZero ratZero))
      ratZero := by
  exact RatEq_trans _ _ _
    (RatEq_symm li_online_zero_angle_identity)
    li_online_zero_angle_zero

private theorem one_sub_neg_one_eq_two :
    RatEq (ratSub ratOne (ratNeg ratOne)) (natRat 2) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl ratOne)
      (BEDC.Derived.LocatedReal.ratNeg_neg_local ratOne))
    (RatEq_symm natRat_two_eq_one_add_one)

theorem li_online_pi_angle_identity :
    RatEq
      (ratMul (natRat 2) (ratSub ratOne (ratNeg ratOne)))
      (ratAdd
        (ratMul
          (ratSub ratOne (ratNeg ratOne))
          (ratSub ratOne (ratNeg ratOne)))
        (ratMul ratZero ratZero)) :=
  li_online_sos_identity (ratNeg ratOne) ratZero cos_neg_one_sin_zero_unit

theorem li_online_pi_angle_four :
    RatEq
      (ratMul (natRat 2) (ratSub ratOne (ratNeg ratOne)))
      (natRat 4) := by
  exact RatEq_trans _ _ _
    (ratMul_respects (RatEq_refl (natRat 2)) one_sub_neg_one_eq_two)
    (natRat_mul 2 2)

theorem li_online_pi_angle_sos_four :
    RatEq
      (ratAdd
        (ratMul
          (ratSub ratOne (ratNeg ratOne))
          (ratSub ratOne (ratNeg ratOne)))
        (ratMul ratZero ratZero))
      (natRat 4) := by
  exact RatEq_trans _ _ _
    (RatEq_symm li_online_pi_angle_identity)
    li_online_pi_angle_four

end BEDC.Derived.RHRoute.LiPhaseGeometry
