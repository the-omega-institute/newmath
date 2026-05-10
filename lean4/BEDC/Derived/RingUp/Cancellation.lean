import BEDC.Derived.RingUp
import BEDC.Derived.AbGroupUp

namespace BEDC.Derived.RingUp

open BEDC.FKernel.Hist

theorem ring_additive_two_sided_cancellation {add : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b')) {a b c : BHist} :
    (hsame (add a c) (add b c) -> hsame a b) ∧
      (hsame (add c a) (add c b) -> hsame a b) := by
  have addRightZero : forall x : BHist, hsame (add x BHist.Empty) x := by
    exact ring_add_right_zero addComm zeroLeft
  have addRightInverse : forall x : BHist, hsame (add x (neg x)) BHist.Empty := by
    exact ring_add_right_inverse addComm negLeft
  constructor
  · intro sameRightProducts
    exact BEDC.Derived.GroupUp.group_right_cancel addAssoc addRightZero addCongr
      addRightInverse sameRightProducts
  · intro sameLeftProducts
    exact BEDC.Derived.GroupUp.group_left_cancel addAssoc zeroLeft addCongr negLeft
      sameLeftProducts

theorem ring_additive_difference_zero_exact {add : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b')) {x y : BHist} :
    hsame (add x (neg y)) BHist.Empty ↔ hsame x y := by
  have addRightZero : forall z : BHist, hsame (add z BHist.Empty) z := by
    exact ring_add_right_zero addComm zeroLeft
  have addRightInverse : forall z : BHist, hsame (add z (neg z)) BHist.Empty := by
    exact ring_add_right_inverse addComm negLeft
  constructor
  · intro differenceZero
    have sameProducts : hsame (add x (neg y)) (add y (neg y)) :=
      hsame_trans differenceZero (hsame_symm (addRightInverse y))
    exact BEDC.Derived.GroupUp.group_right_cancel addAssoc addRightZero addCongr
      addRightInverse sameProducts
  · intro sameXY
    exact hsame_trans (addCongr sameXY (hsame_refl (neg y))) (addRightInverse y)

theorem ring_neg_add {add : BHist -> BHist -> BHist} {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b')) :
    forall x y : BHist, hsame (neg (add x y)) (add (neg x) (neg y)) := by
  have addRightZero : forall x : BHist, hsame (add x BHist.Empty) x := by
    exact ring_add_right_zero addComm zeroLeft
  have addRightInverse : forall x : BHist, hsame (add x (neg x)) BHist.Empty := by
    exact ring_add_right_inverse addComm negLeft
  intro x y
  have pairRightInverse :
      hsame (add (add x y) (add (neg x) (neg y))) BHist.Empty := by
    exact BEDC.Derived.AbGroupUp.abgroup_mul_inverse_pair_collapse
      addAssoc addComm addRightZero addCongr addRightInverse x y
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    addAssoc zeroLeft addRightZero addCongr (negLeft (add x y)) pairRightInverse

theorem ring_negation_classifier_exactness {add : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (add a b) (add a' b'))
    (negCongr : forall {a b : BHist}, hsame a b -> hsame (neg a) (neg b)) :
    forall x y : BHist, hsame (neg x) (neg y) <-> hsame x y := by
  intro x y
  constructor
  · intro sameNeg
    have addRightInverse : forall z : BHist, hsame (add z (neg z)) BHist.Empty := by
      exact ring_add_right_inverse addComm negLeft
    have differenceZero : hsame (add x (neg y)) BHist.Empty := by
      exact hsame_trans (addCongr (hsame_refl x) (hsame_symm sameNeg))
        (addRightInverse x)
    exact Iff.mp
      (ring_additive_difference_zero_exact addAssoc addComm zeroLeft negLeft addCongr)
      differenceZero
  · intro sameXY
    exact negCongr sameXY

end BEDC.Derived.RingUp
