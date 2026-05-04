import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

protected theorem SubgroupCentralizerIntersectionCarrier_simultaneous_self_normalizer_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b t : BHist} :
    SubgroupCentralizerIntersectionCarrier mul a b t ->
      SubgroupCentralizerNormalizer mul inv a t ∧ SubgroupCentralizerNormalizer mul inv b t := by
  intro centralT
  exact And.intro
    (SubgroupCentralizerCarrier_self_normalizes
      assocC leftId rightId mulCongr leftInv rightInv centralT.left)
    (SubgroupCentralizerCarrier_self_normalizes
      assocC leftId rightId mulCongr leftInv rightInv centralT.right)

end BEDC.Derived.SubgroupUp
