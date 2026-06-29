import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedUniformCompletionComparisonUp : Type where
  | mk (L U S R E H C P N : BHist) : LocatedUniformCompletionComparisonUp

end BEDC.Derived
