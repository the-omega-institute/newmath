import BEDC.Derived.GroupUp

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist

protected theorem field_inverse_involutive_nonzero_from_apartness {mul : BHist -> BHist -> BHist}
    {one : BHist} {NonZero : BHist -> Prop} {inv : (a : BHist) -> NonZero a -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul one x) x)
    (rightId : forall x : BHist, hsame (mul x one) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall (a : BHist) (p : NonZero a), hsame (mul (inv a p) a) one)
    (nonzeroEmptyAbsurd : forall x : BHist, NonZero x -> hsame x BHist.Empty -> False)
    {a : BHist} (pa : NonZero a) (pinv : NonZero (inv a pa)) :
    hsame (inv (inv a pa) pinv) a ∧
      (hsame (inv (inv a pa) pinv) BHist.Empty -> False) := by
  have involutive : hsame (inv (inv a pa) pinv) a := by
    exact BEDC.Derived.GroupUp.group_left_right_inverse_uniqueness
      assocC leftId rightId mulCongr
      (leftInv (inv a pa) pinv)
      (leftInv a pa)
  constructor
  · exact involutive
  · intro inverseEmpty
    exact nonzeroEmptyAbsurd a pa (hsame_trans (hsame_symm involutive) inverseEmpty)

end BEDC.Derived.FieldUp
