import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicIntervalCompletionUp : Type where
  | mk (I T S R E H C P N : BHist) : DyadicIntervalCompletionUp
  deriving DecidableEq

end BEDC.Derived
