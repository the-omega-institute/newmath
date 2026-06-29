import BEDC.Derived.LocatedReal.GroundedToleranceKit

set_option maxHeartbeats 2000000

namespace BEDC.Derived.RationalOrderArithUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp
open BEDC.Derived.PadicUp
open BEDC.Derived.RationalUp
open BEDC.Derived.LocatedReal

abbrev Rat : Type :=
  RatNum

def ratCmp (x y : Rat) : Ordering :=
  if ratLtBool x y then Ordering.lt
  else if ratLtBool y x then Ordering.gt
  else Ordering.eq

def cmpLt (x y : Rat) : Prop :=
  ratCmp x y = Ordering.lt

def cmpLe (x y : Rat) : Prop :=
  ratCmp x y = Ordering.lt ∨ ratCmp x y = Ordering.eq

private theorem natLeBool_true_to_le {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      cases b with
      | zero =>
          intro h
          cases h
      | succ b =>
          intro h
          exact Nat.succ_le_succ (ih h)

private theorem ratLtBool_true_to_ratLt {x y : Rat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt intLtUp BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le h)

private theorem ratLt_to_ratLtBool {x y : Rat} :
    ratLt x y -> ratLtBool x y = true := by
  intro h
  unfold ratLtBool
  unfold ratLt intLtUp BEDC.Derived.IntUp.intLt at h
  exact BEDC.Derived.IntUp.natLeBool_true_of_le (Nat.succ_le_of_lt h)

theorem ratCmp_lt_of_ratLt {x y : Rat} :
    ratLt x y -> ratCmp x y = Ordering.lt := by
  intro h
  unfold ratCmp
  rw [ratLt_to_ratLtBool h]
  rfl

theorem ratLt_of_ratCmp_lt {x y : Rat} :
    ratCmp x y = Ordering.lt -> ratLt x y := by
  intro h
  unfold ratCmp at h
  cases ltCase : ratLtBool x y with
  | false =>
      cases yxCase : ratLtBool y x with
      | false =>
          rw [ltCase, yxCase] at h
          cases h
      | true =>
          rw [ltCase, yxCase] at h
          cases h
  | true =>
      exact ratLtBool_true_to_ratLt ltCase

theorem cmpLt_iff_ratLt (x y : Rat) :
    cmpLt x y ↔ ratLt x y := by
  constructor
  · exact ratLt_of_ratCmp_lt
  · exact ratCmp_lt_of_ratLt

theorem ratLt_not_RatEq {x y : Rat} :
    ratLt x y -> RatEq x y -> False := by
  intro hlt same
  unfold ratLt intLtUp BEDC.Derived.IntUp.intLt at hlt
  unfold RatEq at same
  have lenEq := IntPairClassifier_length_eq same
  unfold IntMul ratDenInt at hlt
  rw [lenEq] at hlt
  exact Nat.lt_irrefl _ hlt

theorem ratLt_irrefl (x : Rat) :
    ratLt x x -> False := by
  intro hlt
  exact ratLt_not_RatEq hlt (RatEq_refl x)

theorem ratLt_asymm {x y : Rat} :
    ratLt x y -> ratLt y x -> False := by
  intro xy yx
  exact ratLt_not_ratLe_reverse xy (ratLt_to_ratLe yx)

theorem ratLt_trans {x y z : Rat} :
    ratLt x y -> ratLt y z -> ratLt x z := by
  intro xy yz
  apply ratLe_not_le_to_ratLt
  · exact ratLe_trans (ratLt_to_ratLe xy) (ratLt_to_ratLe yz)
  · intro zx
    exact ratLt_not_ratLe_reverse yz
      (ratLe_trans zx (ratLt_to_ratLe xy))

theorem rat_order_trichotomy (x y : Rat) :
    ratLt x y ∨ RatEq x y ∨ ratLt y x := by
  cases ratLe_decidable x y with
  | inl xy =>
      cases ratLe_decidable y x with
      | inl yx =>
          exact Or.inr (Or.inl (ratLe_antisymm xy yx))
      | inr notYX =>
          exact Or.inl (ratLe_not_le_to_ratLt xy notYX)
  | inr notXY =>
      have yx : ratLe y x := by
        cases ratLe_total x y with
        | inl xy => exact False.elim (notXY xy)
        | inr yx => exact yx
      exact Or.inr (Or.inr (ratLe_not_le_to_ratLt yx notXY))

private def intTwo : BEDC.Derived.PrimeUp.IntegerUp :=
  intOfNat (BHist.e1 NatOne)
    (unary_e1_closed (unary_e1_closed unary_empty))

def ratTwo : Rat :=
  intToRat intTwo

def ratFour : Rat :=
  ratAdd ratTwo ratTwo

def ratDivApart (x y : Rat) (hy : ratApart0 y) : Rat :=
  ratMul x (ratInvApart y hy)

theorem rat_sq_strictMono {a b : Rat} :
    ratLe ratZero a -> ratLt a b ->
      ratLt (ratMul a a) (ratMul b b) := by
  intro aNonneg hlt
  have aLeB : ratLe a b := ratLt_to_ratLe hlt
  have bPositive : ratLt ratZero b :=
    ratLe_lt_trans aNonneg hlt
  have aaLeAB : ratLe (ratMul a a) (ratMul a b) :=
    ratLe_respects (RatEq_refl (ratMul a a)) (ratMul_comm b a)
      (ratMul_le_mul_right aLeB aNonneg)
  have abLtBB : ratLt (ratMul a b) (ratMul b b) :=
    ratMul_lt_mul_right hlt bPositive
  exact ratLe_lt_trans aaLeAB abLtBB

theorem mul_le_mul_nonneg {a b c d : Rat} :
    ratLe a b -> ratLe c d -> ratLe ratZero a -> ratLe ratZero c ->
      ratLe (ratMul a c) (ratMul b d) := by
  intro ab cd aNonneg cNonneg
  have bNonneg : ratLe ratZero b := ratLe_trans aNonneg ab
  exact ratLe_trans
    (ratMul_le_mul_right ab cNonneg)
    (ratMul_le_mul_left cd bNonneg)

theorem add_le_four_of_le_two {a b : Rat} :
    ratLe a ratTwo -> ratLe b ratTwo -> ratLe (ratAdd a b) ratFour := by
  intro aLeTwo bLeTwo
  unfold ratFour
  exact ratLe_add_mono aLeTwo bLeTwo

theorem lt_of_sq_lt_sq_nonneg {a b : Rat} :
    ratLe ratZero a -> ratLe ratZero b ->
      ratLt (ratMul a a) (ratMul b b) -> ratLt a b := by
  intro aNonneg bNonneg sqLt
  cases ratLe_decidable b a with
  | inl ba =>
      have sqReverse : ratLe (ratMul b b) (ratMul a a) :=
        mul_le_mul_nonneg ba ba bNonneg bNonneg
      exact False.elim (ratLt_not_ratLe_reverse sqLt sqReverse)
  | inr notBA =>
      have ab : ratLe a b := by
        cases ratLe_total a b with
        | inl ab => exact ab
        | inr ba => exact False.elim (notBA ba)
      exact ratLe_not_le_to_ratLt ab notBA

theorem sub_pos_of_lt {a b : Rat} :
    ratLt a b -> ratLt ratZero (ratSub b a) := by
  intro h
  apply ratLe_not_le_to_ratLt
  · exact ratSub_nonneg_of_le (ratLt_to_ratLe h)
  · intro nonpos
    have nonneg : ratLe ratZero (ratSub b a) :=
      ratSub_nonneg_of_le (ratLt_to_ratLe h)
    have diffZero : RatEq (ratSub b a) ratZero :=
      ratLe_antisymm nonpos nonneg
    have sameBA : RatEq b a :=
      (ratSub_zero_iff b a).mp diffZero
    exact ratLt_not_RatEq h (RatEq_symm sameBA)

private theorem ratNum_zero_to_RatEq_zero {x : Rat} :
    IntEq x.num intZero -> RatEq x ratZero := by
  intro numZero
  unfold RatEq
  change
    IntEq (IntMul x.num (ratDenInt ratZero))
      (IntMul ratZero.num (ratDenInt x))
  have leftToZero :
      IntEq (IntMul x.num (ratDenInt ratZero)) intZero :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (IntEq_trans (intMul_one_right x.num) numZero)
  have rightToZero :
      IntEq (IntMul ratZero.num (ratDenInt x)) intZero := by
    change IntEq (IntMul intZero (ratDenInt x)) intZero
    exact intMul_zero_left (ratDenInt x)
  exact IntEq_trans leftToZero (IntEq_symm rightToZero)

private theorem ratMul_zero_left (x : Rat) :
    RatEq (ratMul ratZero x) ratZero := by
  apply ratNum_zero_to_RatEq_zero
  unfold ratMul ratZero intToRat
  change IntEq (IntMul intZero x.num) intZero
  exact intMul_zero_left x.num

private theorem ratMul_zero_right (x : Rat) :
    RatEq (ratMul x ratZero) ratZero := by
  exact RatEq_trans (ratMul x ratZero) (ratMul ratZero x) ratZero
    (ratMul_comm x ratZero) (ratMul_zero_left x)

private theorem intStrictPos_num_of_ratPos {x : Rat} :
    ratLt ratZero x -> intLtUp intZero x.num := by
  intro hlt
  unfold ratLt ratZero intToRat at hlt
  change
    intLtUp (IntMul intZero (ratDenInt x))
      (IntMul x.num (ratDenInt ratZero)) at hlt
  have leftZero :
      IntEq (IntMul intZero (ratDenInt x)) intZero :=
    intMul_zero_left (ratDenInt x)
  have rightNum :
      IntEq (IntMul x.num (ratDenInt ratZero)) x.num :=
    IntEq_trans (intMul_left_congr (c := x.num) ratDenInt_zero)
      (intMul_one_right x.num)
  exact intLt_respects leftZero rightNum hlt

private theorem intStrictPos_of_nat_with_sign {sign : BMark} {n : BHist}
    (hn : UnaryHistory n) :
    intLtUp intZero (intOfNatWithSign sign n hn) ->
      sign = BMark.b0 := by
  intro hpos
  cases sign with
  | b0 => rfl
  | b1 =>
      unfold intLtUp intLt intZero intOfNat intToPair at hpos
      change bwordLength BHist.Empty + bwordLength n <
        bwordLength BHist.Empty + bwordLength BHist.Empty at hpos
      rw [BEDC.Derived.NatUp.NatUp_unary_standard_bridge.left] at hpos
      rw [Nat.zero_add, Nat.add_zero] at hpos
      exact False.elim (Nat.not_lt_zero _ hpos)

private theorem intStrictPos_sign_zero {x : RatInt} :
    intLtUp intZero x -> x.sign = BMark.b0 := by
  intro hpos
  cases x with
  | mk sign magnitude carrier =>
      change intLtUp intZero
        (intOfNatWithSign sign magnitude carrier.right) at hpos
      exact intStrictPos_of_nat_with_sign (sign := sign)
        (n := magnitude) carrier.right hpos

private theorem ratInvApart_nonneg_of_pos {y : Rat} (hyPos : ratLt ratZero y) :
    ratLe ratZero (ratInvApart y (ratPositive_num_nonzero hyPos)) := by
  apply ratNonneg_of_num
  cases y with
  | mk num den den_pos =>
      have posNum : intLtUp intZero num :=
        intStrictPos_num_of_ratPos (x := RatNum.mk num den den_pos) hyPos
      have signZero : num.sign = BMark.b0 := intStrictPos_sign_zero posNum
      change intLe intZero
        (intOfNatWithSign num.sign den
          (ratDenCarrier (RatNum.mk num den den_pos)))
      rw [signZero]
      exact intLe_zero_of_nat den
        (ratDenCarrier (RatNum.mk num den den_pos))

private theorem ratInvApart_pos_of_pos {y : Rat} (hyPos : ratLt ratZero y) :
    ratLt ratZero (ratInvApart y (ratPositive_num_nonzero hyPos)) := by
  apply ratLe_not_le_to_ratLt
  · exact ratInvApart_nonneg_of_pos hyPos
  · intro nonpos
    have nonneg :
        ratLe ratZero (ratInvApart y (ratPositive_num_nonzero hyPos)) :=
      ratInvApart_nonneg_of_pos hyPos
    have invZero : RatEq (ratInvApart y (ratPositive_num_nonzero hyPos)) ratZero :=
      ratLe_antisymm nonpos nonneg
    have productZero :
        RatEq (ratMul y (ratInvApart y (ratPositive_num_nonzero hyPos))) ratZero :=
      RatEq_trans _ _ _
        (ratMul_respects (RatEq_refl y) invZero)
        (ratMul_zero_right y)
    have oneZero : RatEq ratOne ratZero :=
      RatEq_trans ratOne
        (ratMul y (ratInvApart y (ratPositive_num_nonzero hyPos)))
        ratZero
        (RatEq_symm (ratInvApart_mul y (ratPositive_num_nonzero hyPos)))
        productZero
    have oneApart : ratApart0 ratOne := by
      unfold ratApart0 ratOne intToRat intOne intOfNat
      exact Or.inr (hsame_refl NatOne)
    exact intApart0_not_zero_pair oneApart (RatEq_zero_num oneZero)

theorem div_pos {a b : Rat} (aPos : ratLt ratZero a) (bPos : ratLt ratZero b) :
    ratLt ratZero (ratDivApart a b (ratPositive_num_nonzero bPos)) := by
  unfold ratDivApart
  let inv := ratInvApart b (ratPositive_num_nonzero bPos)
  have zeroMulInv : RatEq (ratMul ratZero inv) ratZero :=
    ratMul_zero_left inv
  have raw := ratMul_lt_mul_right aPos (ratInvApart_pos_of_pos bPos)
  apply ratLe_not_le_to_ratLt
  · change ratLe ratZero (ratMul a inv)
    exact ratLe_respects
      zeroMulInv
      (RatEq_refl (ratMul a inv))
      (ratLt_to_ratLe raw)
  · intro reverse
    exact ratLt_not_ratLe_reverse raw
      (ratLe_respects
        (RatEq_refl (ratMul a inv))
        (RatEq_symm zeroMulInv)
        reverse)

private theorem ratLt_respects {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> ratLt x y -> ratLt x' y' := by
  intro xx' yy' h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_respects xx' yy' (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects (RatEq_symm yy') (RatEq_symm xx') reverse)

private theorem ratAdd_right_neg_cancel (x y : Rat) :
    RatEq (ratAdd (ratAdd x y) (ratNeg y)) x := by
  exact RatEq_trans _ _ _
    (ratAdd_assoc_local x y (ratNeg y))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x) (ratAdd_neg_local y))
      (ratAdd_zero_right x))

private theorem ratSub_add_cancel_right (x y : Rat) :
    RatEq (ratAdd (ratSub x y) y) x := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_assoc_local x (ratNeg y) y)
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl x) (ratNeg_add_local y))
      (ratAdd_zero_right x))

private theorem ratConstSub_add_neg_left_cancel (c x : Rat) :
    RatEq (ratAdd (ratSub c x) (ratNeg c)) (ratNeg x) := by
  unfold ratSub
  exact RatEq_trans _ _ _
    (ratAdd_assoc_local c (ratNeg x) (ratNeg c))
    (RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl c) (ratAdd_comm (ratNeg x) (ratNeg c)))
      (RatEq_trans _ _ _
        (RatEq_symm (ratAdd_assoc_local c (ratNeg c) (ratNeg x)))
        (RatEq_trans _ _ _
          (ratAdd_respects (ratAdd_neg_local c) (RatEq_refl (ratNeg x)))
          (ratZero_add_left (ratNeg x)))))

private theorem ratLe_add_right_cancel {x x' y : Rat} :
    ratLe (ratAdd x y) (ratAdd x' y) -> ratLe x x' := by
  intro h
  have shifted :
      ratLe (ratAdd (ratAdd x y) (ratNeg y))
        (ratAdd (ratAdd x' y) (ratNeg y)) :=
    ratLe_add_right_mono (x := ratAdd x y) (x' := ratAdd x' y)
      (y := ratNeg y) h
  exact ratLe_respects
    (ratAdd_right_neg_cancel x y)
    (ratAdd_right_neg_cancel x' y)
    shifted

private theorem ratLt_add_right_mono {x x' y : Rat} :
    ratLt x x' -> ratLt (ratAdd x y) (ratAdd x' y) := by
  intro h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_add_right_mono (x := x) (x' := x') (y := y)
      (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h (ratLe_add_right_cancel reverse)

theorem ratTwo_nonneg :
    ratLe ratZero ratTwo := by
  apply ratNonneg_of_num
  unfold ratTwo intTwo intToRat
  exact intLe_zero_of_nat (BHist.e1 NatOne)
    (unary_e1_closed (unary_e1_closed unary_empty))

theorem ratTwo_apart :
    ratApart0 ratTwo := by
  unfold ratApart0 ratTwo intTwo intToRat intOfNat
  exact Or.inl
    (BEDC.Derived.NatUp.NatUnaryStrictPrefix_one_step
      (unary_e1_closed unary_empty))

theorem ratTwo_pos :
    ratLt ratZero ratTwo := by
  apply ratLe_not_le_to_ratLt
  · exact ratTwo_nonneg
  · intro twoLeZero
    have twoZero : RatEq ratTwo ratZero :=
      ratLe_antisymm twoLeZero ratTwo_nonneg
    exact intApart0_not_zero_pair ratTwo_apart (RatEq_zero_num twoZero)

theorem ratFour_pos :
    ratLt ratZero ratFour := by
  unfold ratFour
  have raw :
      ratLt (ratAdd ratZero ratTwo) (ratAdd ratTwo ratTwo) :=
    ratLt_add_right_mono (x := ratZero) (x' := ratTwo)
      (y := ratTwo) ratTwo_pos
  have twoLtFour : ratLt ratTwo (ratAdd ratTwo ratTwo) :=
    ratLt_respects (ratZero_add_left ratTwo) (RatEq_refl _) raw
  exact ratLe_lt_trans ratTwo_nonneg twoLtFour

theorem ratFour_apart :
    ratApart0 ratFour :=
  ratPositive_num_nonzero ratFour_pos

theorem div_by_four_mul_four {y : Rat} :
    RatEq (ratMul (ratDivApart y ratFour ratFour_apart) ratFour) y := by
  unfold ratDivApart
  have invMulFour :
      RatEq (ratMul (ratInvApart ratFour ratFour_apart) ratFour) ratOne :=
    RatEq_trans _ _ _
      (ratMul_comm (ratInvApart ratFour ratFour_apart) ratFour)
      (ratInvApart_mul ratFour ratFour_apart)
  exact RatEq_trans _ _ _
    (ratMul_assoc y (ratInvApart ratFour ratFour_apart) ratFour)
    (RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl y) invMulFour)
      (ratMul_one_right y))

theorem mul_four_lt_of_lt_div_four {x y : Rat} (_yPos : ratLt ratZero y) :
    ratLt x (ratDivApart y ratFour ratFour_apart) ->
      ratLt (ratMul x ratFour) y := by
  intro h
  have raw :
      ratLt (ratMul x ratFour)
        (ratMul (ratDivApart y ratFour ratFour_apart) ratFour) :=
    ratMul_lt_mul_right h ratFour_pos
  exact ratLt_respects (RatEq_refl _) div_by_four_mul_four raw

private theorem ratLe_neg_anti {a b : Rat} :
    ratLe a b -> ratLe (ratNeg b) (ratNeg a) := by
  intro h
  let t := ratAdd (ratNeg a) (ratNeg b)
  have shifted : ratLe (ratAdd a t) (ratAdd b t) :=
    ratLe_add_right_mono (x := a) (x' := b) (y := t) h
  have leftEq : RatEq (ratAdd a t) (ratNeg b) := by
    unfold t
    exact RatEq_trans _ _ _
      (RatEq_symm (ratAdd_assoc_local a (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (ratAdd_respects (ratAdd_neg_local a) (RatEq_refl (ratNeg b)))
        (ratZero_add_left (ratNeg b)))
  have rightEq : RatEq (ratAdd b t) (ratNeg a) := by
    unfold t
    exact RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl b) (ratAdd_comm (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (RatEq_symm (ratAdd_assoc_local b (ratNeg b) (ratNeg a)))
        (RatEq_trans _ _ _
          (ratAdd_respects (ratAdd_neg_local b) (RatEq_refl (ratNeg a)))
          (ratZero_add_left (ratNeg a))))
  exact ratLe_respects leftEq rightEq shifted

private theorem ratLt_neg_anti {a b : Rat} :
    ratLt a b -> ratLt (ratNeg b) (ratNeg a) := by
  intro h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_neg_anti (ratLt_to_ratLe h)
  · intro reverse
    have raw : ratLe (ratNeg (ratNeg b)) (ratNeg (ratNeg a)) :=
      ratLe_neg_anti reverse
    have ba : ratLe b a :=
      ratLe_respects (ratNeg_neg_local b) (ratNeg_neg_local a) raw
    exact ratLt_not_ratLe_reverse h ba

theorem const_sub_strictAnti {a b c : Rat} :
    ratLt a b -> ratLt (ratSub c b) (ratSub c a) := by
  intro h
  have negStep : ratLt (ratNeg b) (ratNeg a) := ratLt_neg_anti h
  have shifted :
      ratLt (ratAdd (ratNeg b) c) (ratAdd (ratNeg a) c) :=
    ratLt_add_right_mono (x := ratNeg b) (x' := ratNeg a)
      (y := c) negStep
  exact ratLt_respects
    (ratAdd_comm (ratNeg b) c)
    (ratAdd_comm (ratNeg a) c)
    shifted

theorem lt_of_const_sub_lt_const_sub {a b c : Rat} :
    ratLt (ratSub c b) (ratSub c a) -> ratLt a b := by
  intro h
  have shifted :
      ratLt (ratAdd (ratSub c b) (ratNeg c))
        (ratAdd (ratSub c a) (ratNeg c)) :=
    ratLt_add_right_mono (x := ratSub c b) (x' := ratSub c a)
      (y := ratNeg c) h
  have negStep : ratLt (ratNeg b) (ratNeg a) :=
    ratLt_respects
      (ratConstSub_add_neg_left_cancel c b)
      (ratConstSub_add_neg_left_cancel c a)
      shifted
  have raw : ratLt (ratNeg (ratNeg a)) (ratNeg (ratNeg b)) :=
    ratLt_neg_anti negStep
  exact ratLt_respects (ratNeg_neg_local a) (ratNeg_neg_local b) raw

theorem lt_of_sub_lt_sub_right {a b c : Rat} :
    ratLt (ratSub a c) (ratSub b c) -> ratLt a b := by
  intro h
  have shifted :
      ratLt (ratAdd (ratSub a c) c) (ratAdd (ratSub b c) c) :=
    ratLt_add_right_mono (x := ratSub a c) (x' := ratSub b c)
      (y := c) h
  exact ratLt_respects
    (ratSub_add_cancel_right a c)
    (ratSub_add_cancel_right b c)
    shifted

end BEDC.Derived.RationalOrderArithUp
