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

end BEDC.Derived.FieldUp
