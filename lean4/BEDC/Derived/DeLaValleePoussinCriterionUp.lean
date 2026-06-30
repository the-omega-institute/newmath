import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DeLaValleePoussinCriterionUp : Type where
  | mk
      (measureRow integralRow uniformIntegrabilityRow convexGrowthRow tailBudgetRow
        regularReadbackRow realSealRow transportRow replayRow provenanceRow localNameCertRow :
          BHist) :
      DeLaValleePoussinCriterionUp
  deriving DecidableEq

end BEDC.Derived
