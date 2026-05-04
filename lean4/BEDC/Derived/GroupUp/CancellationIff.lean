import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

protected theorem group_left_mul_cancel_from_empty_unit_iff {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x, hsame (mul BHist.Empty x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x, hsame (mul (inv x) x) BHist.Empty) {a b c : BHist} :
    hsame (mul a b) (mul a c) <-> hsame b c := by
  constructor
  · intro sameProducts
    exact group_left_cancel assocC leftId mulCongr leftInv sameProducts
  · intro sameTail
    exact mulCongr (hsame_refl a) sameTail

protected theorem group_right_mul_cancel_from_empty_unit_iff {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x, hsame (mul x (inv x)) BHist.Empty) {a b c : BHist} :
    hsame (mul b a) (mul c a) <-> hsame b c := by
  constructor
  · intro sameProducts
    exact group_right_cancel assocC rightId mulCongr rightInv sameProducts
  · intro sameHead
    exact mulCongr sameHead (hsame_refl a)

end BEDC.Derived.GroupUp
