import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist

def FpsSingletonSourceSpec (F : BHist) : Prop :=
  FpsSingletonEmptyHistoryCarrier F ∧ hsame (FpsSingletonCoeff F BHist.Empty) BHist.Empty

theorem FpsSingletonSourceSpec_empty :
    FpsSingletonSourceSpec BHist.Empty ∧
      FpsSingletonClassifier (FpsSingletonCoeff BHist.Empty BHist.Empty) BHist.Empty := by
  have emptyCarrier : FpsSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have coeffLedger :=
    FpsSingletonCoeff_empty_ledger (F := BHist.Empty) (n := BHist.Empty) emptyCarrier
  exact And.intro (And.intro (hsame_refl BHist.Empty) coeffLedger.left) coeffLedger.right

end BEDC.Derived.FpsUp
