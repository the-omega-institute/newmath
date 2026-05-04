import BEDC.Derived.QuotientGroupUp

namespace BEDC.Derived.QuotientGroupUp

open BEDC.FKernel.Hist

theorem CentralizerCosetCarrier_empty_representative_visible_absurd
    {mul : BHist -> BHist -> BHist} {a z : BHist} :
    (CentralizerCosetCarrier mul a BHist.Empty (BHist.e0 z) -> False) ∧
      (CentralizerCosetCarrier mul a BHist.Empty (BHist.e1 z) -> False) := by
  constructor
  · intro carrier
    exact not_hsame_e0_empty carrier.right
  · intro carrier
    exact not_hsame_e1_empty carrier.right

end BEDC.Derived.QuotientGroupUp
