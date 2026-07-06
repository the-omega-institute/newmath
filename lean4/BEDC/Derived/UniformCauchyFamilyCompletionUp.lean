import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive UniformCauchyFamilyCompletionUp : Type where
  | mk (U F T W R E H C P N : BHist) : UniformCauchyFamilyCompletionUp
  deriving DecidableEq

end BEDC.Derived
