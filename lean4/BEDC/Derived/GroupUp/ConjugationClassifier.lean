import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

protected theorem group_conjugation_classifier_exact_from_empty_unit_iff
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    hsame (mul (mul a x) (inv a)) (mul (mul a y) (inv a)) <-> hsame x y := by
  constructor
  · intro sameConj
    have sameXTarget :
        hsame x (mul (mul (inv a) (mul (mul a y) (inv a))) a) := by
      exact (group_conjugation_equation_exact_from_empty_unit_iff
        assocC leftId rightId mulCongr leftInv rightInv).mp sameConj
    have sameYTarget :
        hsame y (mul (mul (inv a) (mul (mul a y) (inv a))) a) := by
      exact (group_conjugation_equation_exact_from_empty_unit_iff
        assocC leftId rightId mulCongr leftInv rightInv).mp
          (hsame_refl (mul (mul a y) (inv a)))
    exact hsame_trans sameXTarget (hsame_symm sameYTarget)
  · intro sameXY
    exact mulCongr (mulCongr (hsame_refl a) sameXY) (hsame_refl (inv a))

end BEDC.Derived.GroupUp
