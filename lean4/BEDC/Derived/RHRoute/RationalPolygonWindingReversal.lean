import BEDC.Derived.RHRoute.RationalPolygonWinding
import BEDC.Derived.RationalOrderArithUp
import BEDC.Derived.LocatedReal.GroundedToleranceKit
import BEDC.Algebra.Rel.IntegerUp

set_option maxHeartbeats 4000000

namespace BEDC.Derived.RHRoute.RationalPolygonWinding

open BEDC.Derived.RationalUp

private theorem natLeBool_true_to_le {a b : Nat} :
    BEDC.Derived.IntUp.natLeBool a b = true -> a ≤ b := by
  induction a generalizing b with
  | zero =>
      intro _h
      exact Nat.zero_le b
  | succ a ih =>
      intro h
      cases b with
      | zero =>
          cases h
      | succ b =>
          exact Nat.succ_le_succ (ih h)

private theorem ratLeBool_true_to_ratLe {x y : Rat} :
    ratLeBool x y = true -> ratLe x y := by
  intro h
  unfold ratLeBool at h
  unfold ratLe BEDC.Derived.RationalUp.intLe
  exact BEDC.Derived.IntUp.pairLe_of_length_order
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (BEDC.Derived.RationalUp.intToPair_carrier _)
    (natLeBool_true_to_le h)

private theorem ratLtBool_true_to_ratLt {x y : Rat} :
    ratLtBool x y = true -> ratLt x y := by
  intro h
  unfold ratLtBool at h
  unfold ratLt BEDC.Derived.RationalUp.intLtUp BEDC.Derived.IntUp.intLt
  exact Nat.lt_of_succ_le (natLeBool_true_to_le h)

private theorem ratLe_to_ratLeBool {x y : Rat} :
    ratLe x y -> ratLeBool x y = true := by
  intro h
  unfold ratLeBool
  unfold ratLe BEDC.Derived.RationalUp.intLe at h
  exact BEDC.Derived.IntUp.natLeBool_true_of_le
    ((BEDC.Derived.IntUp.pairLe_iff_length_order
      (BEDC.Derived.RationalUp.intToPair_carrier _)
      (BEDC.Derived.RationalUp.intToPair_carrier _)).mp h)

private theorem ratLt_to_ratLtBool {x y : Rat} :
    ratLt x y -> ratLtBool x y = true := by
  intro h
  unfold ratLtBool
  unfold ratLt BEDC.Derived.RationalUp.intLtUp BEDC.Derived.IntUp.intLt at h
  exact BEDC.Derived.IntUp.natLeBool_true_of_le (Nat.succ_le_of_lt h)

private theorem ratLtBool_false_of_not_ratLt {x y : Rat} :
    (ratLt x y -> False) -> ratLtBool x y = false := by
  intro notLt
  cases h : ratLtBool x y with
  | false => rfl
  | true => exact False.elim (notLt (ratLtBool_true_to_ratLt h))

private theorem ratLeBool_false_of_not_ratLe {x y : Rat} :
    (ratLe x y -> False) -> ratLeBool x y = false := by
  intro notLe
  cases h : ratLeBool x y with
  | false => rfl
  | true => exact False.elim (notLe (ratLeBool_true_to_ratLe h))

private theorem positive_not_nonpositive {q : Rat} :
    ratLt ratZero q -> ratLe q ratZero -> False := by
  intro pos nonpos
  exact ratLt_not_ratLe_reverse pos nonpos

private theorem negative_not_positive {q : Rat} :
    ratLt q ratZero -> ratLt ratZero q -> False := by
  intro neg pos
  exact ratLt_not_ratLe_reverse neg (ratLt_to_ratLe pos)

private theorem ratLt_respects_local {x x' y y' : Rat} :
    RatEq x x' -> RatEq y y' -> ratLt x y -> ratLt x' y' := by
  intro xx' yy' h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_respects xx' yy' (ratLt_to_ratLe h)
  · intro reverse
    exact ratLt_not_ratLe_reverse h
      (ratLe_respects (RatEq_symm yy') (RatEq_symm xx') reverse)

private theorem ratLe_neg_anti_local {a b : Rat} :
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

private theorem ratLt_neg_anti_local {a b : Rat} :
    ratLt a b -> ratLt (ratNeg b) (ratNeg a) := by
  intro h
  apply ratLe_not_le_to_ratLt
  · exact ratLe_neg_anti_local (ratLt_to_ratLe h)
  · intro reverse
    have raw : ratLe (ratNeg (ratNeg b)) (ratNeg (ratNeg a)) :=
      ratLe_neg_anti_local reverse
    have ba : ratLe b a :=
      ratLe_respects
        (BEDC.Derived.LocatedReal.ratNeg_neg_local b)
        (BEDC.Derived.LocatedReal.ratNeg_neg_local a)
        raw
    exact ratLt_not_ratLe_reverse h ba

private theorem ratNeg_zero_local :
    RatEq (ratNeg ratZero) ratZero := by
  apply ratEq_of_num_den_intEq
  · unfold ratNeg ratZero intToRat
    exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_zero
  · unfold ratNeg ratZero ratDenInt intToRat
    exact IntEq_refl _

theorem rayIntersectionNumerator_swap (a b : RatComplex) :
    RatEq (rayIntersectionNumerator b a)
      (ratNeg (rayIntersectionNumerator a b)) := by
  unfold rayIntersectionNumerator
  exact ratSub_swap_neg (ratMul b.re a.im) (ratMul a.re b.im)

private theorem rayIntersectionNumerator_swap_pos_to_neg
    {a b : RatComplex} :
    ratLt ratZero (rayIntersectionNumerator b a) ->
      ratLt (rayIntersectionNumerator a b) ratZero := by
  intro h
  have negStep :
      ratLt
        (ratNeg (rayIntersectionNumerator b a))
        (ratNeg ratZero) :=
    ratLt_neg_anti_local h
  have leftSame :
      RatEq
        (ratNeg (rayIntersectionNumerator b a))
        (rayIntersectionNumerator a b) :=
    RatEq_trans _ _ _
      (ratNeg_respects (rayIntersectionNumerator_swap a b))
      (BEDC.Derived.LocatedReal.ratNeg_neg_local
        (rayIntersectionNumerator a b))
  exact ratLt_respects_local
    leftSame
    ratNeg_zero_local
    negStep

private theorem rayIntersectionNumerator_pos_of_swap_neg
    {a b : RatComplex} :
    ratLt (rayIntersectionNumerator a b) ratZero ->
      ratLt ratZero (rayIntersectionNumerator b a) := by
  intro h
  have negStep :
      ratLt
        (ratNeg ratZero)
        (ratNeg (rayIntersectionNumerator a b)) :=
    ratLt_neg_anti_local h
  exact ratLt_respects_local
    ratNeg_zero_local
    (RatEq_symm (rayIntersectionNumerator_swap a b))
    negStep

theorem upwardPositiveRayCrossingBool_swap_eq_downward
    (a b : RatComplex) :
    upwardPositiveRayCrossingBool b a =
      downwardPositiveRayCrossingBool a b := by
  unfold upwardPositiveRayCrossingBool downwardPositiveRayCrossingBool
    ratNonPositiveBool ratStrictPositiveBool ratStrictNegativeBool
  cases hbNonpos : ratLeBool b.im ratZero with
  | false =>
      rfl
  | true =>
      cases haPos : ratLtBool ratZero a.im with
      | false =>
          rfl
      | true =>
          have bNonpos : ratLe b.im ratZero :=
            ratLeBool_true_to_ratLe hbNonpos
          have aPos : ratLt ratZero a.im :=
            ratLtBool_true_to_ratLt haPos
          have aNotNonpos : ratLe a.im ratZero -> False :=
            positive_not_nonpositive aPos
          have bNotPos : ratLt ratZero b.im -> False :=
            fun bPos => positive_not_nonpositive bPos bNonpos
          cases hswapNum :
              ratLtBool ratZero (rayIntersectionNumerator b a) with
          | false =>
              have aNotNeg :
                  ratLt (rayIntersectionNumerator a b) ratZero -> False := by
                intro aNeg
                have bPos :
                    ratLt ratZero (rayIntersectionNumerator b a) :=
                  rayIntersectionNumerator_pos_of_swap_neg aNeg
                rw [ratLt_to_ratLtBool bPos] at hswapNum
                cases hswapNum
              have aNegFalse :
                  ratLtBool (rayIntersectionNumerator a b) ratZero = false :=
                ratLtBool_false_of_not_ratLt aNotNeg
              rw [aNegFalse]
          | true =>
              have aNumNeg :
                  ratLt (rayIntersectionNumerator a b) ratZero :=
                rayIntersectionNumerator_swap_pos_to_neg
                  (ratLtBool_true_to_ratLt hswapNum)
              have aNegTrue :
                  ratLtBool (rayIntersectionNumerator a b) ratZero = true :=
                ratLt_to_ratLtBool aNumNeg
              rw [aNegTrue]

theorem downwardPositiveRayCrossingBool_swap_eq_upward
    (a b : RatComplex) :
    downwardPositiveRayCrossingBool b a =
      upwardPositiveRayCrossingBool a b := by
  exact Eq.symm (upwardPositiveRayCrossingBool_swap_eq_downward b a)

private theorem upward_downward_not_both
    (a b : RatComplex) :
    upwardPositiveRayCrossingBool a b = true ->
      downwardPositiveRayCrossingBool a b = true -> False := by
  intro up down
  unfold upwardPositiveRayCrossingBool ratNonPositiveBool
    ratStrictPositiveBool at up
  unfold downwardPositiveRayCrossingBool ratNonPositiveBool
    ratStrictPositiveBool ratStrictNegativeBool at down
  cases haNonpos : ratLeBool a.im ratZero with
  | false =>
      rw [haNonpos] at up
      cases up
  | true =>
      cases hbPos : ratLtBool ratZero b.im with
      | false =>
          rw [haNonpos, hbPos] at up
          cases up
      | true =>
          cases hnumPos : ratLtBool ratZero (rayIntersectionNumerator a b) with
          | false =>
              rw [haNonpos, hbPos, hnumPos] at up
              cases up
          | true =>
              have bPos : ratLt ratZero b.im :=
                ratLtBool_true_to_ratLt hbPos
              rw [ratLeBool_false_of_not_ratLe
                (positive_not_nonpositive bPos)] at down
              cases down

private theorem edgeCrossingUp_reverse_of_up
    {a b : RatComplex}
    (up : upwardPositiveRayCrossingBool a b = true) :
    IntEq (edgeCrossingUp { source := b, target := a })
      (IntNeg (edgeCrossingUp { source := a, target := b })) := by
  have downSwap : downwardPositiveRayCrossingBool b a = true := by
    rw [downwardPositiveRayCrossingBool_swap_eq_upward a b]
    exact up
  have upSwapFalse : upwardPositiveRayCrossingBool b a = false := by
    cases h : upwardPositiveRayCrossingBool b a with
    | false => rfl
    | true =>
        exact False.elim (upward_downward_not_both b a h downSwap)
  unfold edgeCrossingUp
  rw [up]
  rw [upSwapFalse]
  rw [downSwap]
  exact BEDC.Algebra.Rel.IntegerUp_neg_neg intOne

private theorem edgeCrossingUp_reverse_of_down
    {a b : RatComplex}
    (upFalse : upwardPositiveRayCrossingBool a b = false)
    (down : downwardPositiveRayCrossingBool a b = true) :
    IntEq (edgeCrossingUp { source := b, target := a })
      (IntNeg (edgeCrossingUp { source := a, target := b })) := by
  have upSwap : upwardPositiveRayCrossingBool b a = true := by
    rw [upwardPositiveRayCrossingBool_swap_eq_downward a b]
    exact down
  unfold edgeCrossingUp
  rw [upFalse]
  rw [down]
  rw [upSwap]
  exact IntEq_refl intOne

private theorem edgeCrossingUp_reverse_of_zero
    {a b : RatComplex}
    (upFalse : upwardPositiveRayCrossingBool a b = false)
    (downFalse : downwardPositiveRayCrossingBool a b = false) :
    IntEq (edgeCrossingUp { source := b, target := a })
      (IntNeg (edgeCrossingUp { source := a, target := b })) := by
  have upSwapFalse : upwardPositiveRayCrossingBool b a = false := by
    rw [upwardPositiveRayCrossingBool_swap_eq_downward a b]
    exact downFalse
  have downSwapFalse : downwardPositiveRayCrossingBool b a = false := by
    rw [downwardPositiveRayCrossingBool_swap_eq_upward a b]
    exact upFalse
  unfold edgeCrossingUp
  rw [upFalse]
  rw [downFalse]
  rw [upSwapFalse]
  rw [downSwapFalse]
  exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.neg_zero

theorem edgeCrossingUp_reverse (a b : RatComplex) :
    IntEq (edgeCrossingUp { source := b, target := a })
      (IntNeg (edgeCrossingUp { source := a, target := b })) := by
  cases up : upwardPositiveRayCrossingBool a b with
  | true =>
      exact edgeCrossingUp_reverse_of_up up
  | false =>
      cases down : downwardPositiveRayCrossingBool a b with
      | true =>
          exact edgeCrossingUp_reverse_of_down up down
      | false =>
          exact edgeCrossingUp_reverse_of_zero up down

theorem edgeCrossingUp_reverse_cancel (a b : RatComplex) :
    IntEq
      (IntAdd (edgeCrossingUp { source := a, target := b })
        (edgeCrossingUp { source := b, target := a }))
      intZero := by
  let x := edgeCrossingUp { source := a, target := b }
  have reverse :
      IntEq (edgeCrossingUp { source := b, target := a }) (IntNeg x) :=
    edgeCrossingUp_reverse a b
  exact IntEq_trans
    (IntAdd_respects (IntEq_refl x) reverse)
    (IntAdd_neg x)

end BEDC.Derived.RHRoute.RationalPolygonWinding
