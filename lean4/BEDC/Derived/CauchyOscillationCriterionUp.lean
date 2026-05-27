import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyOscillationCriterionUp : Type where
  | mk (O K A U Q R H C P N : BHist) : CauchyOscillationCriterionUp
  deriving DecidableEq

end BEDC.Derived
