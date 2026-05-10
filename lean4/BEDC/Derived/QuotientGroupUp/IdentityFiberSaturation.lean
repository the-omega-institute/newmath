import BEDC.Derived.QuotientGroupUp

namespace BEDC.Derived.QuotientGroupUp

open BEDC.FKernel.Hist
open BEDC.Derived.SubgroupUp

theorem QuotientGroupCentralizerNormalizer_identity_fiber_classifier_saturation
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x y : BHist} :
    let KQ := fun t : BHist => SubgroupCentralizerQuotientKernel mul inv a BHist.Empty t
    (KQ x -> SubgroupCentralizerQuotientKernel mul inv a x y -> KQ y) ∧
      (KQ y -> SubgroupCentralizerQuotientKernel mul inv a x y -> KQ x) := by
  dsimp
  have laws :=
    BEDC.Derived.SubgroupUp.SubgroupCentralizerQuotientKernel_classifier_laws
      assocC leftId rightId mulCongr leftInv rightInv (a := a)
  constructor
  · intro kernelX classifiedXY
    exact laws.right.right kernelX classifiedXY
  · intro kernelY classifiedXY
    exact laws.right.right kernelY (laws.right.left classifiedXY)

end BEDC.Derived.QuotientGroupUp
