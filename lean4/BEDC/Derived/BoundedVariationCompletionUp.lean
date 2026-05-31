import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BoundedVariationCompletionUp : Type where
  | mk (V R D I S Q E H C P N : BHist) : BoundedVariationCompletionUp
  deriving DecidableEq

end BEDC.Derived
