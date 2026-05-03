import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

 theorem field_apart_product_inverse_classifier_exact_from_apartness
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (apartToNonzero : forall {h : BHist}, (hsame h BHist.Empty -> False) -> NonZero h)
    {a b c d : BHist} (pabApart : hsame (mul a b) BHist.Empty -> False)
    (pcdApart : hsame (mul c d) BHist.Empty -> False)
    (pa : NonZero a) (pb : NonZero b) (pc : NonZero c) (pd : NonZero d) :
    hsame (mul a b) (mul c d) <->
      hsame (mul (inv b pb) (inv a pa)) (mul (inv d pd) (inv c pc)) := by
  let pab : NonZero (mul a b) := apartToNonzero pabApart
  let pcd : NonZero (mul c d) := apartToNonzero pcdApart
  have reverseAB :
      hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa)) := by
    exact field_inverse_product_reverse_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  have reverseCD :
      hsame (inv (mul c d) pcd) (mul (inv d pd) (inv c pc)) := by
    exact field_inverse_product_reverse_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pcd pc pd
  constructor
  · intro sameProduct
    have sameIndexed :
        hsame (inv (mul a b) pab) (inv (mul c d) pcd) := by
      exact field_inverse_congruence_from_apartness
        assocC leftId rightId mulCongr leftInv rightInv sameProduct pab pcd
    exact hsame_trans (hsame_symm reverseAB) (hsame_trans sameIndexed reverseCD)
  · intro sameReverse
    have sameIndexed :
        hsame (inv (mul a b) pab) (inv (mul c d) pcd) := by
      exact hsame_trans reverseAB (hsame_trans sameReverse (hsame_symm reverseCD))
    exact field_inverse_cancel_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pcd sameIndexed

end BEDC.Derived.FieldUp
