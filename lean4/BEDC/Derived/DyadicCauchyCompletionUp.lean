import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicCauchyCompletionUp : Type where
  | mk (D W E R S H C P N : BHist) : DyadicCauchyCompletionUp
  deriving DecidableEq

end BEDC.Derived
