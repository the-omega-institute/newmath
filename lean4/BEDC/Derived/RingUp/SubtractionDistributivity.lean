import BEDC.Derived.RingUp

namespace BEDC.Derived.RingUp

open BEDC.FKernel.Hist

theorem ring_left_distributivity_over_subtraction
    {add mul : BHist -> BHist -> BHist}
    {neg : BHist -> BHist}
    (addAssoc : forall x y z : BHist, hsame (add (add x y) z) (add x (add y z)))
    (addComm : forall x y : BHist, hsame (add x y) (add y x))
    (zeroLeft : forall x : BHist, hsame (add BHist.Empty x) x)
    (negLeft : forall x : BHist, hsame (add (neg x) x) BHist.Empty)
    (addCongr :
      forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
        hsame (add a b) (add a' b'))
    (mulCongr :
      forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
        hsame (mul a b) (mul a' b'))
    (leftDistrib :
      forall x y z : BHist, hsame (mul x (add y z)) (add (mul x y) (mul x z)))
    (rightDistrib :
      forall x y z : BHist, hsame (mul (add x y) z) (add (mul x z) (mul y z))) :
    forall a b c : BHist,
      hsame (mul a (add b (neg c))) (add (mul a b) (neg (mul a c))) := by
  intro a b c
  have distributed :
      hsame (mul a (add b (neg c))) (add (mul a b) (mul a (neg c))) := by
    exact leftDistrib a b (neg c)
  have negProduct : hsame (mul a (neg c)) (neg (mul a c)) := by
    exact ring_mul_neg_right_eq_neg_mul addAssoc addComm zeroLeft negLeft addCongr
      mulCongr leftDistrib rightDistrib a c
  have transported :
      hsame (add (mul a b) (mul a (neg c))) (add (mul a b) (neg (mul a c))) := by
    exact addCongr (hsame_refl (mul a b)) negProduct
  exact hsame_trans distributed transported

end BEDC.Derived.RingUp
