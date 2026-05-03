import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.QuotientGroupUp

open BEDC.FKernel.Hist
open BEDC.Derived.SubgroupUp

theorem QuotientGroupCentralizerNormalizer_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a : BHist} :
    SubgroupCentralizerNormalizer mul inv a BHist.Empty := by
  intro x centralX
  have invEmpty : hsame (inv BHist.Empty) BHist.Empty := by
    exact hsame_trans (hsame_symm (leftId (inv BHist.Empty))) (rightInv BHist.Empty)
  have conjugateSame :
      hsame (mul (mul BHist.Empty x) (inv BHist.Empty)) x := by
    exact hsame_trans (mulCongr (leftId x) invEmpty) (rightId x)
  exact hsame_trans (mulCongr conjugateSame (hsame_refl a))
    (hsame_trans centralX (mulCongr (hsame_refl a) (hsame_symm conjugateSame)))

theorem QuotientGroupCentralizerNormalizer_empty_hsame_transport_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (invCongr : forall {x y : BHist}, hsame x y -> hsame (inv x) (inv y))
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a t : BHist} :
    hsame BHist.Empty t -> SubgroupCentralizerNormalizer mul inv a t := by
  intro emptyT x centralX
  have conjugateToEmpty :
      hsame (mul (mul t x) (inv t))
        (mul (mul BHist.Empty x) (inv BHist.Empty)) := by
    exact mulCongr (mulCongr (hsame_symm emptyT) (hsame_refl x)) (invCongr (hsame_symm emptyT))
  have emptyConjugateCentral :
      SubgroupCentralizerCarrier mul a (mul (mul BHist.Empty x) (inv BHist.Empty)) := by
    exact QuotientGroupCentralizerNormalizer_empty_unit
      leftId rightId mulCongr rightInv x centralX
  exact hsame_trans (mulCongr conjugateToEmpty (hsame_refl a))
    (hsame_trans emptyConjugateCentral
      (mulCongr (hsame_refl a) (hsame_symm conjugateToEmpty)))

end BEDC.Derived.QuotientGroupUp
