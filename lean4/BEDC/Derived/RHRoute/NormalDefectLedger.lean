import BEDC.Derived.RHRoute.JensenTuranDegree2

namespace BEDC.Derived.RHRoute.NormalDefectLedger

set_option maxHeartbeats 2000000

open BEDC.Derived.RationalUp
open BEDC.Derived.RationalOrderArithUp

abbrev Rat : Type :=
  RatNum

def defect (r h : Rat) : Rat :=
  ratNeg (ratMul r h)

def ratListSum : List Rat -> Rat
  | [] => ratZero
  | x :: xs => ratAdd x (ratListSum xs)

def heightSum : List Rat -> Rat :=
  ratListSum

def heightEnergy : List Rat -> Rat
  | [] => ratZero
  | h :: hs => ratAdd (ratMul h h) (heightEnergy hs)

def ledgerD (r : Rat) : List Rat -> Rat
  | [] => ratZero
  | h :: hs => ratAdd (defect r h) (ledgerD r hs)

def ledgerE (r : Rat) : List Rat -> Rat
  | [] => ratZero
  | h :: hs =>
      let d := defect r h
      ratAdd (ratMul d d) (ledgerE r hs)

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

private theorem ratNeg_zero_local :
    RatEq (ratNeg ratZero) ratZero := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg ratZero intToRat
    change IntEq (IntNeg intZero) intZero
    exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_zero
  · unfold ratNeg ratZero ratDenInt intToRat
    exact IntEq_refl _

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

private theorem ratNeg_neg_mul_local (x y : Rat) :
    RatEq (ratMul (ratNeg x) y) (ratMul x (ratNeg y)) := by
  exact RatEq_trans _ _ _
    (ratMul_neg_left_local x y)
    (RatEq_symm (ratMul_neg_right_local x y))

private theorem intAdd_four_swap (a b c d : RatInt) :
    IntEq (IntAdd (IntAdd a b) (IntAdd c d))
      (IntAdd (IntAdd a c) (IntAdd b d)) := by
  let R := BEDC.Algebra.Rel.IntegerUp_RelCommRing
  exact R.trans (R.add_assoc a b (IntAdd c d))
    (R.trans
      (R.add_congr (R.refl a) (R.symm (R.add_assoc b c d)))
      (R.trans
        (R.add_congr (R.refl a)
          (R.add_congr (R.add_comm b c) (R.refl d)))
        (R.trans
          (R.add_congr (R.refl a) (R.add_assoc c b d))
          (R.symm (R.add_assoc a c (IntAdd b d))))))

private theorem intNeg_add_local (a b : RatInt) :
    IntEq (IntNeg (IntAdd a b)) (IntAdd (IntNeg a) (IntNeg b)) := by
  let R := BEDC.Algebra.Rel.IntegerUp_RelCommRing
  have paired :
      IntEq (IntAdd (IntAdd a b) (IntAdd (IntNeg a) (IntNeg b)))
        (IntAdd (IntAdd a (IntNeg a)) (IntAdd b (IntNeg b))) :=
    intAdd_four_swap a b (IntNeg a) (IntNeg b)
  have collapsed :
      IntEq (IntAdd (IntAdd a (IntNeg a)) (IntAdd b (IntNeg b)))
        (IntAdd intZero intZero) :=
    IntAdd_respects (IntAdd_neg a) (IntAdd_neg b)
  have zeroed :
      IntEq (IntAdd (IntAdd a b) (IntAdd (IntNeg a) (IntNeg b))) intZero :=
    IntEq_trans paired (IntEq_trans collapsed (IntAdd_zero_left intZero))
  exact IntEq_symm
    (R.eq_neg_of_add_eq_zero (a := IntAdd a b)
      (b := IntAdd (IntNeg a) (IntNeg b)) zeroed)

private theorem ratNeg_add_local (x y : Rat) :
    RatEq (ratNeg (ratAdd x y)) (ratAdd (ratNeg x) (ratNeg y)) := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg ratAdd
    let yd := intOfNat y.den (ratDenCarrier y)
    let xd := intOfNat x.den (ratDenCarrier x)
    have split :
        IntEq
          (IntNeg (IntAdd (IntMul x.num yd) (IntMul y.num xd)))
          (IntAdd
            (IntNeg (IntMul x.num yd))
            (IntNeg (IntMul y.num xd))) :=
      intNeg_add_local (IntMul x.num yd) (IntMul y.num xd)
    have moveNeg :
        IntEq
          (IntAdd
            (IntNeg (IntMul x.num yd))
            (IntNeg (IntMul y.num xd)))
          (IntAdd
            (IntMul (IntNeg x.num) yd)
            (IntMul (IntNeg y.num) xd)) :=
      IntAdd_respects
        (IntEq_symm (BEDC.Algebra.Rel.IntegerUp_neg_mul x.num yd))
        (IntEq_symm (BEDC.Algebra.Rel.IntegerUp_neg_mul y.num xd))
    exact IntEq_trans split moveNeg
  · exact IntEq_trans (ratDenInt_add x y)
      (IntEq_symm (ratDenInt_add (ratNeg x) (ratNeg y)))

private theorem ratAdd_assoc_local (x y z : Rat) :
    RatEq (ratAdd (ratAdd x y) z) (ratAdd x (ratAdd y z)) :=
  BEDC.Derived.LocatedReal.ratAdd_assoc_local x y z

private theorem ratAdd_nonneg_local {x y : Rat} :
    ratLe ratZero x -> ratLe ratZero y -> ratLe ratZero (ratAdd x y) := by
  intro hx hy
  have raw :
      ratLe (ratAdd ratZero ratZero) (ratAdd x y) :=
    BEDC.Real.RatNumKernel.ratAdd_le_add hx hy
  exact ratLe_respects (ratZero_add_left ratZero) (RatEq_refl _) raw

private theorem ratMul_pos_local {x y : Rat} :
    ratLt ratZero x -> ratLt ratZero y -> ratLt ratZero (ratMul x y) := by
  intro hx hy
  have raw : ratLt (ratMul ratZero y) (ratMul x y) :=
    ratMul_lt_mul_right hx hy
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_left
    (RatEq_symm (ratMul_zero_left_local y)) raw

private theorem ratAdd_right_cancel_RatEq_local {x y c : Rat} :
    RatEq (ratAdd x c) (ratAdd y c) -> RatEq x y := by
  intro h
  have shifted : RatEq
      (ratAdd (ratAdd x c) (ratNeg c))
      (ratAdd (ratAdd y c) (ratNeg c)) :=
    ratAdd_respects h (RatEq_refl (ratNeg c))
  have leftCancel : RatEq (ratAdd (ratAdd x c) (ratNeg c)) x :=
    RatEq_trans _ _ _
      (ratAdd_assoc_local x c (ratNeg c))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl x)
          (BEDC.Derived.LocatedReal.ratAdd_neg_local c))
        (ratAdd_zero_right x))
  have rightCancel : RatEq (ratAdd (ratAdd y c) (ratNeg c)) y :=
    RatEq_trans _ _ _
      (ratAdd_assoc_local y c (ratNeg c))
      (RatEq_trans _ _ _
        (ratAdd_respects (RatEq_refl y)
          (BEDC.Derived.LocatedReal.ratAdd_neg_local c))
        (ratAdd_zero_right y))
  exact RatEq_trans _ _ _
    (RatEq_symm leftCancel)
    (RatEq_trans _ _ _ shifted rightCancel)

private theorem ratSub_add_cancel_right_local (x y : Rat) :
    RatEq (ratAdd (ratSub x y) y) x := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_assoc_local x (ratNeg y) y)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x)
        (BEDC.Derived.LocatedReal.ratNeg_add_local y))
      (ratAdd_zero_right x))

private theorem ratMul_sub_right_local (a b c : Rat) :
    RatEq (ratMul (ratSub a b) c)
      (ratSub (ratMul a c) (ratMul b c)) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (BEDC.Real.RatNumKernel.ratMul_add_right a (ratNeg b) c)
    (ratAdd_respects (RatEq_refl (ratMul a c))
      (ratMul_neg_left_local b c))

private theorem ratSub_add_left_same_local (a b : Rat) :
    RatEq (ratAdd (ratSub a b) b) a :=
  ratSub_add_cancel_right_local a b

private theorem ratMul_add_right_factor_local (a b c : Rat) :
    RatEq (ratAdd (ratMul a c) (ratMul b c))
      (ratMul (ratAdd a b) c) :=
  RatEq_symm (BEDC.Real.RatNumKernel.ratMul_add_right a b c)

private theorem ratMul_add_left_factor_local (a b c : Rat) :
    RatEq (ratAdd (ratMul a b) (ratMul a c))
      (ratMul a (ratAdd b c)) :=
  RatEq_symm (BEDC.Real.RatNumKernel.ratMul_add_left a b c)

theorem defect_linear_identity (r h : Rat) :
    RatEq (defect r h) (ratNeg (ratMul r h)) :=
  RatEq_refl _

theorem ledgerD_identity (r : Rat) :
    ∀ hs : List Rat,
      RatEq (ledgerD r hs) (ratNeg (ratMul r (heightSum hs)))
  | [] => by
      change RatEq ratZero (ratNeg (ratMul r ratZero))
      exact RatEq_symm
        (RatEq_trans _ _ _
          (ratNeg_respects (ratMul_zero_right_local r))
          ratNeg_zero_local)
  | h :: hs => by
      change
        RatEq
          (ratAdd (defect r h) (ledgerD r hs))
          (ratNeg (ratMul r (ratAdd h (heightSum hs))))
      have ih := ledgerD_identity r hs
      have lhs :
          RatEq
            (ratAdd (defect r h) (ledgerD r hs))
            (ratAdd (ratNeg (ratMul r h))
              (ratNeg (ratMul r (heightSum hs)))) :=
        ratAdd_respects (RatEq_refl _) ih
      have rhsExpand :
          RatEq
            (ratNeg (ratMul r (ratAdd h (heightSum hs))))
            (ratAdd (ratNeg (ratMul r h))
              (ratNeg (ratMul r (heightSum hs)))) := by
        exact RatEq_trans _ _ _
          (ratNeg_respects
            (BEDC.Real.RatNumKernel.ratMul_add_left r h (heightSum hs)))
          (ratNeg_add_local (ratMul r h) (ratMul r (heightSum hs)))
      exact RatEq_trans _ _ _ lhs (RatEq_symm rhsExpand)

private theorem defect_square_identity (r h : Rat) :
    RatEq (ratMul (defect r h) (defect r h))
      (ratMul (ratMul r r) (ratMul h h)) := by
  unfold defect
  have removeNeg :
      RatEq
        (ratMul (ratNeg (ratMul r h)) (ratNeg (ratMul r h)))
        (ratMul (ratMul r h) (ratMul r h)) :=
    ratNeg_mul_neg_local (ratMul r h) (ratMul r h)
  have reassocLeft :
      RatEq
        (ratMul (ratMul r h) (ratMul r h))
        (ratMul r (ratMul h (ratMul r h))) :=
    ratMul_assoc r h (ratMul r h)
  have inner :
      RatEq
        (ratMul h (ratMul r h))
        (ratMul r (ratMul h h)) := by
    exact RatEq_trans _ _ _
      (RatEq_symm (ratMul_assoc h r h))
      (RatEq_trans _ _ _
        (ratMul_respects (ratMul_comm h r) (RatEq_refl h))
        (ratMul_assoc r h h))
  have outer :
      RatEq
        (ratMul r (ratMul h (ratMul r h)))
        (ratMul r (ratMul r (ratMul h h))) :=
    ratMul_respects (RatEq_refl r) inner
  have fold :
      RatEq
        (ratMul r (ratMul r (ratMul h h)))
        (ratMul (ratMul r r) (ratMul h h)) :=
    RatEq_symm (ratMul_assoc r r (ratMul h h))
  exact RatEq_trans _ _ _ removeNeg
    (RatEq_trans _ _ _ reassocLeft
      (RatEq_trans _ _ _ outer fold))

theorem ledgerE_identity (r : Rat) :
    ∀ hs : List Rat,
      RatEq (ledgerE r hs)
        (ratMul (ratMul r r) (heightEnergy hs))
  | [] => by
      change RatEq ratZero (ratMul (ratMul r r) ratZero)
      exact RatEq_symm (ratMul_zero_right_local (ratMul r r))
  | h :: hs => by
      change
        RatEq
          (ratAdd (ratMul (defect r h) (defect r h)) (ledgerE r hs))
          (ratMul (ratMul r r)
            (ratAdd (ratMul h h) (heightEnergy hs)))
      have ih := ledgerE_identity r hs
      have lhs :
          RatEq
            (ratAdd (ratMul (defect r h) (defect r h)) (ledgerE r hs))
            (ratAdd
              (ratMul (ratMul r r) (ratMul h h))
              (ratMul (ratMul r r) (heightEnergy hs))) :=
        ratAdd_respects (defect_square_identity r h) ih
      have rhsFactor :
          RatEq
            (ratAdd
              (ratMul (ratMul r r) (ratMul h h))
              (ratMul (ratMul r r) (heightEnergy hs)))
            (ratMul (ratMul r r)
              (ratAdd (ratMul h h) (heightEnergy hs))) :=
        ratMul_add_left_factor_local (ratMul r r) (ratMul h h)
          (heightEnergy hs)
      exact RatEq_trans _ _ _ lhs rhsFactor

theorem ledgerE_nonneg (r : Rat) :
    ∀ hs : List Rat, ratLe ratZero (ledgerE r hs)
  | [] => by
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | h :: hs => by
      change
        ratLe ratZero
          (ratAdd (ratMul (defect r h) (defect r h)) (ledgerE r hs))
      exact ratAdd_nonneg_local
        (BEDC.Derived.RHRoute.JensenTuranDegree2.ratMul_self_nonneg
          (defect r h))
        (ledgerE_nonneg r hs)

theorem heightEnergy_nonneg :
    ∀ hs : List Rat, ratLe ratZero (heightEnergy hs)
  | [] => by
      change ratLe ratZero ratZero
      exact ratLe_refl ratZero
  | h :: hs => by
      change ratLe ratZero
        (ratAdd (ratMul h h) (heightEnergy hs))
      exact ratAdd_nonneg_local
        (BEDC.Derived.RHRoute.JensenTuranDegree2.ratMul_self_nonneg h)
        (heightEnergy_nonneg hs)

private theorem ratNeg_pos_of_neg_local {x : Rat} :
    ratLt x ratZero -> ratLt ratZero (ratNeg x) := by
  intro h
  have subPos : ratLt ratZero (ratSub ratZero x) :=
    sub_pos_of_lt h
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
    subPos
    (BEDC.Derived.LocatedReal.ratZero_sub_eq_neg x)

theorem defect_neg_parameter (r h : Rat) :
    RatEq (defect (ratNeg r) h) (ratNeg (defect r h)) := by
  unfold defect
  exact ratNeg_respects (ratMul_neg_left_local r h)

theorem ledgerE_neg_parameter (r : Rat) :
    ∀ hs : List Rat, RatEq (ledgerE (ratNeg r) hs) (ledgerE r hs)
  | hs => by
      have left := ledgerE_identity (ratNeg r) hs
      have square :
          RatEq
            (ratMul (ratMul (ratNeg r) (ratNeg r)) (heightEnergy hs))
            (ratMul (ratMul r r) (heightEnergy hs)) :=
        ratMul_respects (ratNeg_mul_neg_local r r)
          (RatEq_refl (heightEnergy hs))
      exact RatEq_trans _ _ _ left
        (RatEq_trans _ _ _ square
          (RatEq_symm (ledgerE_identity r hs)))

theorem ledgerE_positive_of_square_positive
    (r : Rat) (hs : List Rat) :
    ratLt ratZero (ratMul r r) ->
      ratLt ratZero (heightEnergy hs) ->
        ratLt ratZero (ledgerE r hs) := by
  intro hr hW
  have productPos :
      ratLt ratZero (ratMul (ratMul r r) (heightEnergy hs)) :=
    ratMul_pos_local hr hW
  exact BEDC.Real.RatNumKernel.ratLt_of_RatEq_right
    productPos
    (RatEq_symm (ledgerE_identity r hs))

theorem ledgerE_zero_forces_parameter_square_zero
    (r : Rat) (hs : List Rat) :
    RatEq (ledgerE r hs) ratZero ->
      ratLt ratZero (heightEnergy hs) ->
        RatEq (ratMul r r) ratZero := by
  intro hE hW
  have productZero :
      RatEq (ratMul (ratMul r r) (heightEnergy hs)) ratZero :=
    RatEq_trans _ _ _
      (RatEq_symm (ledgerE_identity r hs))
      hE
  have sqNonneg :
      ratLe ratZero (ratMul r r) :=
    BEDC.Derived.RHRoute.JensenTuranDegree2.ratMul_self_nonneg r
  cases rat_order_trichotomy ratZero (ratMul r r) with
  | inl sqPos =>
      have productPos :
          ratLt ratZero (ratMul (ratMul r r) (heightEnergy hs)) :=
        ratMul_pos_local sqPos hW
      exact False.elim
        (ratLt_not_RatEq productPos (RatEq_symm productZero))
  | inr rest =>
      cases rest with
      | inl sqZero =>
          exact RatEq_symm sqZero
      | inr sqNeg =>
          exact False.elim
            (ratLt_not_ratLe_reverse sqNeg sqNonneg)

theorem rat_square_eq_zero_forces_zero (r : Rat) :
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

theorem ledgerE_zero_forces_parameter_zero
    (r : Rat) (hs : List Rat) :
    RatEq (ledgerE r hs) ratZero ->
      ratLt ratZero (heightEnergy hs) ->
        RatEq r ratZero := by
  intro hE hW
  exact rat_square_eq_zero_forces_zero r
    (ledgerE_zero_forces_parameter_square_zero r hs hE hW)

def ratNatLedger (n : Nat) : Rat :=
  BEDC.Real.RatNumKernel.ratNat n

def concreteHeights : List Rat :=
  [ratNatLedger 1, ratNatLedger 2]

def concreteParameter : Rat :=
  ratNatLedger 3

theorem concrete_heightSum :
    RatEq (heightSum concreteHeights) (ratNatLedger 3) := by
  unfold concreteHeights heightSum ratListSum ratNatLedger
  change
    RatEq
      (ratAdd (BEDC.Real.RatNumKernel.ratNat 1)
        (ratAdd (BEDC.Real.RatNumKernel.ratNat 2) ratZero))
      (BEDC.Real.RatNumKernel.ratNat 3)
  exact RatEq_trans _ _ _
    (ratAdd_respects (RatEq_refl _)
      (ratAdd_zero_right (BEDC.Real.RatNumKernel.ratNat 2)))
    (BEDC.Real.RatNumLogEnclosure.ratNat_add 1 2)

theorem concrete_heightEnergy :
    RatEq (heightEnergy concreteHeights) (ratNatLedger 5) := by
  unfold concreteHeights heightEnergy ratNatLedger
  change
    RatEq
      (ratAdd
        (ratMul (BEDC.Real.RatNumKernel.ratNat 1)
          (BEDC.Real.RatNumKernel.ratNat 1))
        (ratAdd
          (ratMul (BEDC.Real.RatNumKernel.ratNat 2)
            (BEDC.Real.RatNumKernel.ratNat 2))
          ratZero))
      (BEDC.Real.RatNumKernel.ratNat 5)
  have tail :
      RatEq
        (ratAdd
          (ratMul (BEDC.Real.RatNumKernel.ratNat 2)
            (BEDC.Real.RatNumKernel.ratNat 2))
          ratZero)
        (BEDC.Real.RatNumKernel.ratNat 4) :=
    RatEq_trans _ _ _
      (ratAdd_zero_right
        (ratMul (BEDC.Real.RatNumKernel.ratNat 2)
          (BEDC.Real.RatNumKernel.ratNat 2)))
      (BEDC.Real.RatNumLogEnclosure.ratNat_mul 2 2)
  have fold :
      RatEq
        (ratAdd
          (ratMul (BEDC.Real.RatNumKernel.ratNat 1)
            (BEDC.Real.RatNumKernel.ratNat 1))
          (ratAdd
            (ratMul (BEDC.Real.RatNumKernel.ratNat 2)
              (BEDC.Real.RatNumKernel.ratNat 2))
            ratZero))
        (ratAdd (BEDC.Real.RatNumKernel.ratNat 1)
          (BEDC.Real.RatNumKernel.ratNat 4)) :=
    ratAdd_respects
      (BEDC.Real.RatNumLogEnclosure.ratNat_mul 1 1)
      tail
  exact RatEq_trans _ _ _ fold
    (BEDC.Real.RatNumLogEnclosure.ratNat_add 1 4)

theorem concrete_ledgerD :
    RatEq (ledgerD concreteParameter concreteHeights)
      (ratNeg (ratNatLedger 9)) := by
  unfold concreteParameter
  have base := ledgerD_identity (ratNatLedger 3) concreteHeights
  have product :
      RatEq
        (ratMul (ratNatLedger 3) (heightSum concreteHeights))
        (ratNatLedger 9) := by
    exact RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl (ratNatLedger 3)) concrete_heightSum)
      (BEDC.Real.RatNumLogEnclosure.ratNat_mul 3 3)
  exact RatEq_trans _ _ _ base
    (ratNeg_respects product)

theorem concrete_ledgerE :
    RatEq (ledgerE concreteParameter concreteHeights)
      (ratNatLedger 45) := by
  unfold concreteParameter
  have base := ledgerE_identity (ratNatLedger 3) concreteHeights
  have product :
      RatEq
        (ratMul (ratMul (ratNatLedger 3) (ratNatLedger 3))
          (heightEnergy concreteHeights))
        (ratNatLedger 45) := by
    exact RatEq_trans _ _ _
      (ratMul_respects
        (BEDC.Real.RatNumLogEnclosure.ratNat_mul 3 3)
        concrete_heightEnergy)
      (BEDC.Real.RatNumLogEnclosure.ratNat_mul 9 5)
  exact RatEq_trans _ _ _ base product

end BEDC.Derived.RHRoute.NormalDefectLedger
