import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp
open BEDC.FKernel.Hist

theorem group_inverse_empty_iff {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {x : BHist} :
    hsame (inv x) BHist.Empty <-> hsame x BHist.Empty := by
  constructor
  · intro invEmpty
    have emptyInv :
        hsame (inv BHist.Empty) BHist.Empty :=
      group_inverse_identity (mul := mul) (e := BHist.Empty) (inv := inv) rightId leftInv
    exact group_inverse_cancel_from_laws assocC leftId rightId mulCongr leftInv rightInv
      (hsame_trans invEmpty (hsame_symm emptyInv))
  · intro xEmpty
    have invCongr :
        hsame (inv x) (inv BHist.Empty) :=
      group_inverse_congruence_from_laws assocC leftId rightId mulCongr leftInv rightInv xEmpty
    have emptyInv :
        hsame (inv BHist.Empty) BHist.Empty :=
      group_inverse_identity (mul := mul) (e := BHist.Empty) (inv := inv) rightId leftInv
    exact hsame_trans invCongr emptyInv

end BEDC.Derived.GroupUp
