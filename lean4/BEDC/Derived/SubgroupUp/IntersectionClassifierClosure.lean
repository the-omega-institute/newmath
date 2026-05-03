import BEDC.Derived.SubgroupUp

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

protected theorem SubgroupCentralizerIntersectionClassifier_mul_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    {a b x x' y y' : BHist} :
    SubgroupCentralizerIntersectionClassifier mul a b x x' ->
      SubgroupCentralizerIntersectionClassifier mul a b y y' ->
        SubgroupCentralizerIntersectionClassifier mul a b (mul x y) (mul x' y') := by
  intro left right
  exact And.intro
    (BEDC.Derived.SubgroupUp.SubgroupCentralizerIntersectionCarrier_mul_closed_from_empty_unit
      assocC rightId mulCongr left.left right.left)
    (And.intro
      (BEDC.Derived.SubgroupUp.SubgroupCentralizerIntersectionCarrier_mul_closed_from_empty_unit
        assocC rightId mulCongr left.right.left right.right.left)
      (mulCongr left.right.right right.right.right))

end BEDC.Derived.SubgroupUp
