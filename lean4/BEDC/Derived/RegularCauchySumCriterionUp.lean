import BEDC.FKernel.Hist

namespace BEDC.Derived.RegularCauchySumCriterionUp

open BEDC.FKernel.Hist

inductive RegularCauchySumCriterionUp : Type where
  | mk (A B WA WB D L R E H C P N : BHist) : RegularCauchySumCriterionUp
  deriving DecidableEq

end BEDC.Derived.RegularCauchySumCriterionUp
