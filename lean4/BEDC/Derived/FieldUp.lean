import BEDC.FKernel.Hist
import BEDC.Derived.GroupUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

theorem field_inverse_congruence_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (sameAB : hsame a b) (p : NonZero a) (q : NonZero b) :
    hsame (inv a p) (inv b q) := by
  have transportedLeft : hsame (mul (inv a p) b) one := by
    exact hsame_trans
      (hsame_symm (mulCongr (hsame_refl (inv a p)) sameAB))
      (leftInv a p)
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    assocC
    leftId
    rightId
    mulCongr
    transportedLeft
    (rightInv b q)

theorem field_inverse_cancel_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (p : NonZero a) (q : NonZero b) :
    hsame (inv a p) (inv b q) -> hsame a b := by
  intro sameInv
  have transportedLeft : hsame (mul (inv b q) a) one := by
    exact hsame_trans
      (hsame_symm (mulCongr sameInv (hsame_refl a)))
      (leftInv a p)
  exact hsame_symm
    (BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
      assocC
      leftId
      rightId
      mulCongr
      (rightInv b q)
      transportedLeft)

 theorem field_inverse_product_reverse_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one)
    {a b : BHist} (pab : NonZero (mul a b)) (pa : NonZero a) (pb : NonZero b) :
    hsame (inv (mul a b) pab) (mul (inv b pb) (inv a pa)) := by
  have reverseRight : hsame (mul (mul a b) (mul (inv b pb) (inv a pa))) one := by
    have inner :
        hsame (mul b (mul (inv b pb) (inv a pa))) (inv a pa) := by
      exact hsame_trans (hsame_symm (assocC b (inv b pb) (inv a pa)))
        (hsame_trans (mulCongr (rightInv b pb) (hsame_refl (inv a pa)))
          (leftId (inv a pa)))
    exact hsame_trans (assocC a b (mul (inv b pb) (inv a pa)))
      (hsame_trans (mulCongr (hsame_refl a) inner) (rightInv a pa))
  exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
    assocC
    leftId
    rightId
    mulCongr
    (leftInv (mul a b) pab)
    reverseRight

 theorem field_mul_inverse_right_cancel_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall (a : BHist) (p : NonZero a), hsame (mul a (inv a p)) one) :
    forall (a b : BHist) (pb : NonZero b),
      hsame (mul (mul a b) (inv b pb)) a := by
  intro a b pb
  have reassoc :
      hsame (mul (mul a b) (inv b pb)) (mul a (mul b (inv b pb))) := by
    exact assocC a b (inv b pb)
  have cancelTail : hsame (mul a (mul b (inv b pb))) (mul a one) := by
    exact mulCongr (hsame_refl a) (rightInv b pb)
  exact hsame_trans reassoc (hsame_trans cancelTail (rightId a))

end BEDC.Derived.FieldUp
