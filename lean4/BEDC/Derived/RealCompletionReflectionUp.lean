import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive RealCompletionReflectionUp : Type where
  | mk (C R S D E F H K P N : BEDC.FKernel.Hist.BHist) :
      RealCompletionReflectionUp
  deriving DecidableEq

end BEDC.Derived
