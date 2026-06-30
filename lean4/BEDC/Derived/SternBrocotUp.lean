import BEDC.Algebra.Rel.IntegerUp
import BEDC.Derived.GcdUp
import BEDC.Derived.PadicUp.IntegerTower
import BEDC.Derived.RationalUp.FieldLaws

namespace BEDC.Derived.SternBrocotUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength bwordLength_append)
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp
open BEDC.Derived.IntUp

abbrev IntegerUp := BEDC.Derived.PrimeUp.IntegerUp
abbrev IntRel := BEDC.Derived.RationalUp.IntEq

def intRing : BEDC.Algebra.Rel.RelCommRing IntegerUp IntRel :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

def PositiveFraction : Type :=
  RatNum

def intDen (x : PositiveFraction) : IntegerUp :=
  intOfNat x.den (ratDenCarrier x)

def denominatorSumPos (x y : PositiveFraction) :
    NatUnaryStrictPrefix NatOne (append x.den y.den) ∨
      hsame (append x.den y.den) NatOne := by
  have xUnary : UnaryHistory x.den := ratDenCarrier x
  have yUnary : UnaryHistory y.den := ratDenCarrier y
  have sumUnary : UnaryHistory (append x.den y.den) :=
    unary_append_closed xUnary yUnary
  have oneLen : bwordLength NatOne = 1 :=
    NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty
  have xOneLe : 1 ≤ bwordLength x.den := by
    cases x.den_pos with
    | inl strict =>
        have lt := NatUnaryStrictPrefix_length_lt (unary_e1_closed unary_empty) strict
        rw [oneLen] at lt
        exact Nat.le_of_lt lt
    | inr same =>
        have len := congrArg bwordLength same
        rw [oneLen] at len
        rw [len]
        exact Nat.le_refl 1
  have yOneLe : 1 ≤ bwordLength y.den := by
    cases y.den_pos with
    | inl strict =>
        have lt := NatUnaryStrictPrefix_length_lt (unary_e1_closed unary_empty) strict
        rw [oneLen] at lt
        exact Nat.le_of_lt lt
    | inr same =>
        have len := congrArg bwordLength same
        rw [oneLen] at len
        rw [len]
        exact Nat.le_refl 1
  have sumLen :
      bwordLength (append x.den y.den) = bwordLength x.den + bwordLength y.den :=
    bwordLength_append x.den y.den
  have oneLtSum : bwordLength NatOne < bwordLength (append x.den y.den) := by
    rw [oneLen, sumLen]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 1)
      (Nat.add_le_add xOneLe yOneLe)
  exact Or.inl
    (NatUnaryStrictPrefix_of_length_lt (unary_e1_closed unary_empty) sumUnary oneLtSum)

def mediant (x y : PositiveFraction) : PositiveFraction :=
  { num := intRing.add x.num y.num
    den := append x.den y.den
    den_pos := denominatorSumPos x y }

theorem mediant_num (x y : PositiveFraction) :
    (mediant x y).num = intRing.add x.num y.num := by
  rfl

theorem mediant_den (x y : PositiveFraction) :
    hsame (mediant x y).den (append x.den y.den) := by
  rfl

theorem intDen_mediant (x y : PositiveFraction) :
    IntRel (intDen (mediant x y)) (intRing.add (intDen x) (intDen y)) := by
  unfold intDen intRing
  change
    BEDC.Derived.IntUp.IntPairClassifier
      (intToPair (intOfNat (append x.den y.den) (ratDenCarrier (mediant x y))))
      (intToPair
        (IntAdd (intOfNat x.den (ratDenCarrier x))
          (intOfNat y.den (ratDenCarrier y))))
  have sumCarrier :
      BEDC.Derived.IntUp.IntPairCarrier (append x.den y.den) BHist.Empty :=
    ⟨unary_append_closed (ratDenCarrier x) (ratDenCarrier y), unary_empty⟩
  have sumPair :
      BEDC.Derived.IntUp.IntPairClassifier
        (intToPair (intOfNat (append x.den y.den) (ratDenCarrier (mediant x y))))
        (pairAdd
          (intToPair (intOfNat x.den (ratDenCarrier x)))
          (intToPair (intOfNat y.den (ratDenCarrier y)))) := by
    unfold intOfNat intToPair pairAdd
    exact IntPairClassifier_equivalence_fields.right.right.left sumCarrier
  have addPair :
      BEDC.Derived.IntUp.IntPairClassifier
        (intToPair
          (IntAdd (intOfNat x.den (ratDenCarrier x))
            (intOfNat y.den (ratDenCarrier y))))
        (pairAdd
          (intToPair (intOfNat x.den (ratDenCarrier x)))
          (intToPair (intOfNat y.den (ratDenCarrier y)))) :=
    intAdd_pair_classifier (intOfNat x.den (ratDenCarrier x))
      (intOfNat y.den (ratDenCarrier y))
  exact IntPairClassifier_equivalence_fields.right.right.right.right.left
    sumPair
    (IntPairClassifier_equivalence_fields.right.right.right.left addPair)

def crossDet (x y : PositiveFraction) : IntegerUp :=
  intRing.add
    (intRing.mul (intDen x) y.num)
    (intRing.neg (intRing.mul x.num (intDen y)))

def FareyAdjacent (x y : PositiveFraction) : Prop :=
  IntRel (crossDet x y) intRing.one

theorem fareyAdjacent_cross_eq_one {x y : PositiveFraction} :
    FareyAdjacent x y -> IntRel (crossDet x y) intRing.one := by
  intro adjacent
  exact adjacent

namespace RelCommRingDeterminant

variable {A : Type u} {r : A -> A -> Prop}
variable (R : BEDC.Algebra.Rel.RelCommRing A r)

private theorem sub_add_cancel (x y : A) :
    r (R.add (R.add x (R.neg y)) y) x := by
  exact R.trans (R.add_assoc x (R.neg y) y)
    (R.trans (R.add_left_congr x (R.neg_add y)) (R.add_zero x))

private theorem add_right_cancel {a b c : A} :
    r (R.add a c) (R.add b c) -> r a b := by
  intro h
  exact R.trans (R.symm (R.add_zero a))
    (R.trans
      (R.add_left_congr a (R.symm (R.add_neg c)))
      (R.trans
        (R.symm (R.add_assoc a c (R.neg c)))
        (R.trans
          (R.add_right_congr h (R.neg c))
          (R.trans
            (R.add_assoc b c (R.neg c))
            (R.trans
              (R.add_left_congr b (R.add_neg c))
              (R.add_zero b))))))

private theorem add_cancel_middle (x y z : A) :
    r (R.add (R.add x (R.neg z)) (R.add y z)) (R.add x y) := by
  exact R.trans (R.symm (R.add_assoc (R.add x (R.neg z)) y z))
    (R.trans
      (R.add_right_congr
        (R.trans
          (R.add_assoc x (R.neg z) y)
          (R.trans
            (R.add_left_congr x (R.add_comm (R.neg z) y))
            (R.symm (R.add_assoc x y (R.neg z)))))
        z)
      (sub_add_cancel R (R.add x y) z))

theorem left_mediant_det
    (a b c d : A) :
    r
      (R.add
        (R.mul b (R.add a c))
        (R.neg (R.mul a (R.add b d))))
      (R.add (R.mul b c) (R.neg (R.mul a d))) := by
  let ba := R.mul b a
  let bc := R.mul b c
  let ab := R.mul a b
  let ad := R.mul a d
  let ab_ad := R.add ab ad
  have expand :
      r
        (R.add
          (R.mul b (R.add a c))
          (R.neg (R.mul a (R.add b d))))
        (R.add (R.add ba bc) (R.neg ab_ad)) :=
    R.add_congr
      (R.left_distrib b a c)
      (R.neg_congr (R.left_distrib a b d))
  have core :
      r (R.add (R.add ba bc) (R.neg ab_ad))
        (R.add bc (R.neg ad)) := by
    apply add_right_cancel R (c := ab_ad)
    exact R.trans
      (sub_add_cancel R (R.add ba bc) ab_ad)
      (R.trans
        (R.trans
          (R.add_right_congr (R.mul_comm b a) bc)
          (R.add_comm ab bc))
        (R.symm (add_cancel_middle R bc ab ad)))
  exact R.trans expand core

theorem right_mediant_det
    (a b c d : A) :
    r
      (R.add
        (R.mul (R.add b d) c)
        (R.neg (R.mul (R.add a c) d)))
      (R.add (R.mul b c) (R.neg (R.mul a d))) := by
  let bc := R.mul b c
  let dc := R.mul d c
  let ad := R.mul a d
  let cd := R.mul c d
  let ad_cd := R.add ad cd
  have expand :
      r
        (R.add
          (R.mul (R.add b d) c)
          (R.neg (R.mul (R.add a c) d)))
        (R.add (R.add bc dc) (R.neg ad_cd)) :=
    R.add_congr
      (R.right_distrib b d c)
      (R.neg_congr (R.right_distrib a c d))
  have core :
      r (R.add (R.add bc dc) (R.neg ad_cd))
        (R.add bc (R.neg ad)) := by
    apply add_right_cancel R (c := ad_cd)
    exact R.trans
      (sub_add_cancel R (R.add bc dc) ad_cd)
      (R.trans
        (R.add_left_congr bc (R.mul_comm d c))
        (R.trans
          (R.symm (add_cancel_middle R bc cd ad))
          (R.add_left_congr (R.add bc (R.neg ad))
            (R.symm (R.add_comm ad cd)))))
  exact R.trans expand core

end RelCommRingDeterminant

theorem fareyAdjacent_left_mediant
    {x y : PositiveFraction} :
    FareyAdjacent x y -> FareyAdjacent x (mediant x y) := by
  intro adjacent
  have denEq : IntRel (intDen (mediant x y)) (intRing.add (intDen x) (intDen y)) :=
    intDen_mediant x y
  have normalized :
      IntRel (crossDet x (mediant x y))
        (intRing.add
          (intRing.mul (intDen x) (intRing.add x.num y.num))
          (intRing.neg
            (intRing.mul x.num (intRing.add (intDen x) (intDen y))))) := by
    unfold crossDet
    exact intRing.add_congr
      (intRing.mul_congr (intRing.refl (intDen x)) (intRing.refl (intRing.add x.num y.num)))
      (intRing.neg_congr
        (intRing.mul_congr (intRing.refl x.num) denEq))
  have detEq :
      IntRel
        (intRing.add
          (intRing.mul (intDen x) (intRing.add x.num y.num))
          (intRing.neg
            (intRing.mul x.num (intRing.add (intDen x) (intDen y)))))
        (crossDet x y) := by
    exact RelCommRingDeterminant.left_mediant_det intRing
      x.num (intDen x) y.num (intDen y)
  exact intRing.trans normalized (intRing.trans detEq adjacent)

theorem fareyAdjacent_mediant_right
    {x y : PositiveFraction} :
    FareyAdjacent x y -> FareyAdjacent (mediant x y) y := by
  intro adjacent
  have denEq : IntRel (intDen (mediant x y)) (intRing.add (intDen x) (intDen y)) :=
    intDen_mediant x y
  have normalized :
      IntRel (crossDet (mediant x y) y)
        (intRing.add
          (intRing.mul (intRing.add (intDen x) (intDen y)) y.num)
          (intRing.neg
            (intRing.mul (intRing.add x.num y.num) (intDen y)))) := by
    unfold crossDet
    exact intRing.add_congr
      (intRing.mul_congr denEq (intRing.refl y.num))
      (intRing.neg_congr
        (intRing.mul_congr (intRing.refl (intRing.add x.num y.num))
          (intRing.refl (intDen y))))
  have detEq :
      IntRel
        (intRing.add
          (intRing.mul (intRing.add (intDen x) (intDen y)) y.num)
          (intRing.neg
            (intRing.mul (intRing.add x.num y.num) (intDen y))))
        (crossDet x y) := by
    exact RelCommRingDeterminant.right_mediant_det intRing
      x.num (intDen x) y.num (intDen y)
  exact intRing.trans normalized (intRing.trans detEq adjacent)

theorem fareyAdjacent_mediant_neighbors
    {x y : PositiveFraction} :
    FareyAdjacent x y ->
      FareyAdjacent x (mediant x y) ∧ FareyAdjacent (mediant x y) y := by
  intro adjacent
  exact ⟨fareyAdjacent_left_mediant adjacent,
    fareyAdjacent_mediant_right adjacent⟩

end BEDC.Derived.SternBrocotUp
