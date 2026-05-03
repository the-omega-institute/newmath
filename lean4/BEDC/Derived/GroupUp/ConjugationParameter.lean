import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

protected theorem group_conjugation_parameter_hsame_congr_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {s t x : BHist} :
    hsame s t -> hsame (mul (mul s x) (inv s)) (mul (mul t x) (inv t)) := by
  intro sameST
  have sameInv : hsame (inv s) (inv t) :=
    group_inverse_congruence_from_laws assocC leftId rightId mulCongr leftInv rightInv sameST
  exact mulCongr (mulCongr sameST (hsame_refl x)) sameInv

end BEDC.Derived.GroupUp
