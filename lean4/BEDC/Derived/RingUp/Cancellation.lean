import BEDC.Derived.RingUp

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

end BEDC.Derived.RingUp
