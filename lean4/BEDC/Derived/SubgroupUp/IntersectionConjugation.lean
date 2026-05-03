import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

theorem SubgroupCentralizerIntersectionCarrier_self_conjugation_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b t x : BHist} :
    SubgroupCentralizerIntersectionCarrier mul a b t ->
      SubgroupCentralizerIntersectionCarrier mul a b x ->
        SubgroupCentralizerIntersectionCarrier mul a b (mul (mul t x) (inv t)) ∧
          SubgroupCentralizerIntersectionCarrier mul a b
            (mul (mul (inv t) x) (inv (inv t))) := by
  intro centralT centralX
  have normalizesA : SubgroupCentralizerNormalizer mul inv a t :=
    SubgroupCentralizerCarrier_self_normalizes
      assocC leftId rightId mulCongr leftInv rightInv centralT.left
  have normalizesB : SubgroupCentralizerNormalizer mul inv b t :=
    SubgroupCentralizerCarrier_self_normalizes
      assocC leftId rightId mulCongr leftInv rightInv centralT.right
  exact And.intro
    (And.intro (normalizesA.left x centralX.left) (normalizesB.left x centralX.right))
    (And.intro (normalizesA.right x centralX.left) (normalizesB.right x centralX.right))

end BEDC.Derived.SubgroupUp
