import BEDC.Derived.FieldUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

protected theorem field_inverse_product_reverse_nonzero_from_one_apartness
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (zeroLeft : forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty)
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (oneApartEmpty : hsame one BHist.Empty -> False)
    (nonzeroOfApartEmpty : forall x : BHist, (hsame x BHist.Empty -> False) -> NonZero x)
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    {a b : BHist} (pab : NonZero (mul a b)) (pa : NonZero a) (pb : NonZero b) :
    NonZero (mul (inv b pb) (inv a pa)) := by
  have inverseProductNonZero : NonZero (inv (mul a b) pab) := by
    exact field_inverse_nonzero_from_one_apartness
      mulCongr zeroLeft leftInv oneApartEmpty nonzeroOfApartEmpty pab
  have reverseProduct :
      hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa)) := by
    exact field_inverse_product_reverse_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  exact nonzeroTransport reverseProduct inverseProductNonZero

protected theorem field_inverse_product_reverse_apart_empty_from_one_apartness
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (zeroLeft : forall x : BHist, hsame (mul BHist.Empty x) BHist.Empty)
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    (oneApartEmpty : hsame one BHist.Empty -> False)
    (nonzeroOfApartEmpty : forall x : BHist, (hsame x BHist.Empty -> False) -> NonZero x)
    (nonzeroTransport : forall {a b : BHist}, hsame a b -> NonZero a -> NonZero b)
    (nonzeroApartEmpty : forall {x : BHist}, NonZero x -> hsame x BHist.Empty -> False)
    {a b : BHist} (pab : NonZero (mul a b)) (pa : NonZero a) (pb : NonZero b) :
    hsame (mul (inv b pb) (inv a pa)) BHist.Empty -> False := by
  have reverseProductNonZero :
      NonZero (mul (inv b pb) (inv a pa)) := by
    exact BEDC.Derived.FieldUp.field_inverse_product_reverse_nonzero_from_one_apartness
      assocC leftId rightId mulCongr zeroLeft leftInv rightInv oneApartEmpty
      nonzeroOfApartEmpty nonzeroTransport pab pa pb
  exact nonzeroApartEmpty reverseProductNonZero

protected theorem field_inverse_product_reverse_apart_empty_transport_from_product_hsame
    {mul : BHist -> BHist -> BHist} {one : BHist} {NonZero : BHist -> Prop}
    {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b a' b' : BHist} (sameProduct : hsame (mul a b) (mul a' b'))
    (pab : NonZero (mul a b)) (pab' : NonZero (mul a' b'))
    (pa : NonZero a) (pb : NonZero b) (pa' : NonZero a') (pb' : NonZero b') :
    (hsame (mul (inv b pb) (inv a pa)) BHist.Empty -> False) ->
      hsame (mul (inv b' pb') (inv a' pa')) BHist.Empty -> False := by
  intro reverseApart reverseEmpty
  have sourceReverse :
      hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa)) := by
    exact field_inverse_product_reverse_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab pa pb
  have targetReverse :
      hsame (inv (mul a' b') pab') (mul (inv b' pb') (inv a' pa')) := by
    exact field_inverse_product_reverse_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv pab' pa' pb'
  have inverseProductSame :
      hsame (inv (mul a b) pab) (inv (mul a' b') pab') := by
    exact field_inverse_congruence_from_apartness
      assocC leftId rightId mulCongr leftInv rightInv sameProduct pab pab'
  have reverseSame :
      hsame (mul (inv b pb) (inv a pa)) (mul (inv b' pb') (inv a' pa')) := by
    exact hsame_trans (hsame_symm sourceReverse)
      (hsame_trans inverseProductSame targetReverse)
  exact reverseApart (hsame_trans reverseSame reverseEmpty)

end BEDC.Derived.FieldUp
