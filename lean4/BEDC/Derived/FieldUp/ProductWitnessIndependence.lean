import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_affine_product_witness_independence
    {add mul : BHist -> BHist -> BHist} {neg : BHist -> BHist} {one : BHist}
    {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (addRightId : forall x : BHist, hsame (add x BHist.Empty) x)
    (negRight : forall x : BHist, hsame (add x (neg x)) BHist.Empty)
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {A B D x q : BHist} (pA pA' : NonZero A) (pB pB' : NonZero B) :
    hsame (add (mul (mul A x) B) D) (add (mul (mul A x) B) D) ∧
      hsame (mul (inv A pA) (mul (add q (neg D)) (inv B pB)))
        (mul (inv A pA') (mul (add q (neg D)) (inv B pB'))) := by
  have _offsetRightId : hsame (add D BHist.Empty) D := addRightId D
  have _offsetNegRight : hsame (add D (neg D)) BHist.Empty := negRight D
  have sameInvA : hsame (inv A pA) (inv A pA') := by
    exact field_inverse_congruence_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv (hsame_refl A) pA pA'
  have sameInvB : hsame (inv B pB) (inv B pB') := by
    exact field_inverse_congruence_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv (hsame_refl B) pB pB'
  constructor
  · exact hsame_refl (add (mul (mul A x) B) D)
  · exact mulCongr sameInvA
      (mulCongr (hsame_refl (add q (neg D))) sameInvB)

end BEDC.Derived.FieldUp
