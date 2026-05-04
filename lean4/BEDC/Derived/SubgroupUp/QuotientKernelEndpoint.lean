import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

protected theorem SubgroupCentralizerQuotientKernel_left_endpoint_right_centralizer_mul_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y c : BHist} :
    SubgroupCentralizerQuotientKernel mul inv a x y ->
      SubgroupCentralizerCarrier mul a c ->
        SubgroupCentralizerQuotientKernel mul inv a (mul x c) y := by
  intro kernel centralC
  have certificateRows :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizer_certificate_target_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  have mulClosed :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u ->
        SubgroupCentralizerCarrier mul a v -> SubgroupCentralizerCarrier mul a (mul u v) :=
    certificateRows.right.right.left
  have invClosed :
      forall {u : BHist}, SubgroupCentralizerCarrier mul a u ->
        SubgroupCentralizerCarrier mul a (inv u) :=
    certificateRows.right.right.right.left
  have carrierTransport :
      forall {u v : BHist}, SubgroupCentralizerCarrier mul a u -> hsame u v ->
        SubgroupCentralizerCarrier mul a v :=
    certificateRows.right.right.right.right
  have normalizesC : SubgroupCentralizerNormalizer mul inv a c :=
    SubgroupCentralizerCarrier_self_normalizes
      assocC leftId rightId mulCongr leftInv rightInv centralC
  have normalizesXC : SubgroupCentralizerNormalizer mul inv a (mul x c) :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerNormalizer_mul_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv kernel.left normalizesC
  have centralInvC : SubgroupCentralizerCarrier mul a (inv c) :=
    invClosed centralC
  have productCentral :
      SubgroupCentralizerCarrier mul a (mul (inv c) (mul (inv x) y)) :=
    mulClosed centralInvC kernel.right.right
  have invProductSame :
      hsame (inv (mul x c)) (mul (inv c) (inv x)) :=
    BEDC.Derived.GroupUp.group_inverse_mul_reverse
      assocC leftId rightId mulCongr leftInv rightInv x c
  have displayedKernel :
      hsame (mul (inv c) (mul (inv x) y)) (mul (inv (mul x c)) y) := by
    exact hsame_trans (hsame_symm (assocC (inv c) (inv x) y))
      (mulCongr (hsame_symm invProductSame) (hsame_refl y))
  exact And.intro normalizesXC
    (And.intro kernel.right.left (carrierTransport productCentral displayedKernel))

end BEDC.Derived.SubgroupUp
