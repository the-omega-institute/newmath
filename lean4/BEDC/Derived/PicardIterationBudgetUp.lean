import BEDC.FKernel.Hist

namespace BEDC.Derived.PicardIterationBudgetUp

open BEDC.FKernel.Hist

inductive PicardIterationBudgetUp : Type where
  | mk
      (seed contractionModulus iterateWindow dyadicBudget endpointHandoff
        transport replay provenance localName : BHist) :
      PicardIterationBudgetUp
  deriving DecidableEq

theorem PicardIterationBudgetUp_nonempty :
    Nonempty PicardIterationBudgetUp := by
  exact
    ⟨PicardIterationBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty⟩

end BEDC.Derived.PicardIterationBudgetUp
