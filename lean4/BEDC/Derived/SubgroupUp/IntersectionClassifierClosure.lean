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

protected theorem SubgroupCentralizerIntersectionClassifier_inv_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b x y : BHist} :
    SubgroupCentralizerIntersectionClassifier mul a b x y ->
      SubgroupCentralizerIntersectionClassifier mul a b (inv x) (inv y) := by
  intro classified
  have invCongr : forall {u v : BHist}, hsame u v -> hsame (inv u) (inv v) :=
    BEDC.Derived.GroupUp.group_inverse_congruence_from_laws
      assocC leftId rightId mulCongr leftInv rightInv
  exact And.intro
    (BEDC.Derived.SubgroupUp.SubgroupCentralizerIntersectionCarrier_inv_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv classified.left)
    (And.intro
      (BEDC.Derived.SubgroupUp.SubgroupCentralizerIntersectionCarrier_inv_closed_from_empty_unit
        assocC leftId rightId mulCongr leftInv rightInv classified.right.left)
      (invCongr classified.right.right))

end BEDC.Derived.SubgroupUp
