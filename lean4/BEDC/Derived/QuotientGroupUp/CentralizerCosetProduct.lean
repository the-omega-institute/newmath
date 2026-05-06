import BEDC.Derived.QuotientGroupUp

namespace BEDC.Derived.QuotientGroupUp

open BEDC.FKernel.Hist
open BEDC.Derived.SubgroupUp

theorem CentralizerCosetCarrier_representative_product_closure
    {mul : BHist -> BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    {a x y h1 h2 : BHist} :
    CentralizerCosetCarrier mul a x h1 ->
      CentralizerCosetCarrier mul a y h2 ->
        CentralizerCosetCarrier mul a (mul x y) (mul h1 h2) := by
  intro carrierX carrierY
  exact And.intro
    (BEDC.Derived.SubgroupUp.SubgroupCentralizerCarrier_mul_closed_from_empty_unit
      assocC rightId mulCongr carrierX.left carrierY.left)
    (mulCongr carrierX.right carrierY.right)

end BEDC.Derived.QuotientGroupUp
