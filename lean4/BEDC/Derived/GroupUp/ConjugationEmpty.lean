import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist

protected theorem group_conjugation_empty_exact_from_empty_unit {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x : BHist} :
    hsame (mul (mul a x) (inv a)) BHist.Empty <-> hsame x BHist.Empty := by
  have normalizedTarget : hsame (mul (mul (inv a) BHist.Empty) a) BHist.Empty := by
    exact hsame_trans (assocC (inv a) BHist.Empty a)
      (hsame_trans (mulCongr (hsame_refl (inv a)) (leftId a)) (leftInv a))
  constructor
  · intro sameConjugate
    have solved :
        hsame x (mul (mul (inv a) BHist.Empty) a) := by
      exact Iff.mp
        (group_conjugation_equation_exact_from_empty_unit_iff
          assocC leftId rightId mulCongr leftInv rightInv)
        sameConjugate
    exact hsame_trans solved normalizedTarget
  · intro sameEmpty
    exact Iff.mpr
      (group_conjugation_equation_exact_from_empty_unit_iff
        assocC leftId rightId mulCongr leftInv rightInv)
      (hsame_trans sameEmpty (hsame_symm normalizedTarget))

end BEDC.Derived.GroupUp
