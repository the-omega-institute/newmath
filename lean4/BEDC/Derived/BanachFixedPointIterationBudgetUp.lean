import BEDC.FKernel.Hist

namespace BEDC.Derived.BanachFixedPointIterationBudgetUp

open BEDC.FKernel.Hist

inductive BanachFixedPointIterationBudgetUp : Type where
  | mk
      (metric contraction initial picardLedger ratioTailBudget regSeqHandoff completeBoundary
        transport replay provenance localName : BHist) :
      BanachFixedPointIterationBudgetUp
  deriving DecidableEq

theorem BanachFixedPointIterationBudgetUp_nonempty :
    Nonempty BanachFixedPointIterationBudgetUp := by
  exact
    ⟨BanachFixedPointIterationBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty⟩

end BEDC.Derived.BanachFixedPointIterationBudgetUp
