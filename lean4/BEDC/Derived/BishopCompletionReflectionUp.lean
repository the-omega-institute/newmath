import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive BishopCompletionReflectionUp : Type where
  | mk (R S D M U E H C P N : BEDC.FKernel.Hist.BHist) :
      BishopCompletionReflectionUp
  deriving DecidableEq

end BEDC.Derived
