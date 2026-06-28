import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SeparatedCauchyCompletionLimitUp : Type where
  | mk (S R D Q E H T P N : BHist) : SeparatedCauchyCompletionLimitUp

end BEDC.Derived
