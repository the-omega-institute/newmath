import BEDC.Derived.GroupUp.Centralizer

namespace BEDC.Derived.SubgroupUp

open BEDC.FKernel.Hist

def SubgroupCentralizerCarrier (mul : BHist -> BHist -> BHist) (a x : BHist) : Prop :=
  hsame (mul x a) (mul a x)

def SubgroupCentralizerNormalizer
    (mul : BHist -> BHist -> BHist) (inv : BHist -> BHist) (a t : BHist) : Prop :=
  forall x : BHist, SubgroupCentralizerCarrier mul a x ->
    SubgroupCentralizerCarrier mul a (mul (mul t x) (inv t))

protected theorem SubgroupCentralizerCarrier_mul_closed_from_empty_unit
    {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    {a x y : BHist} :
    SubgroupCentralizerCarrier mul a x -> SubgroupCentralizerCarrier mul a y ->
      SubgroupCentralizerCarrier mul a (mul x y) := by
  intro centralX centralY
  have closedEmpty :
      hsame (mul (mul (mul x y) a) BHist.Empty)
        (mul (mul a (mul x y)) BHist.Empty) := by
    exact BEDC.Derived.GroupUp.group_centralizer_mul_closed_empty_context
      assocC mulCongr centralX centralY
  exact hsame_trans (hsame_symm (rightId (mul (mul x y) a)))
    (hsame_trans closedEmpty (rightId (mul a (mul x y))))

protected theorem SubgroupCentralizerCarrier_self_normalizer_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a t : BHist} :
    SubgroupCentralizerCarrier mul a t -> SubgroupCentralizerNormalizer mul inv a t := by
  intro centralT x centralX
  have centralInvT : SubgroupCentralizerCarrier mul a (inv t) := by
    exact BEDC.Derived.GroupUp.group_centralizer_inv_closed_from_empty_unit
      assocC leftId rightId mulCongr leftInv rightInv centralT
  have centralTX : SubgroupCentralizerCarrier mul a (mul t x) := by
    exact BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
      assocC rightId mulCongr centralT centralX
  exact BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
    assocC rightId mulCongr centralTX centralInvT

end BEDC.Derived.SubgroupUp
