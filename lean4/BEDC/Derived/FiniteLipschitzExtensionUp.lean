import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteLipschitzExtensionUp : Type where
  | mk (X A L B G W R S H C P N : BHist) : FiniteLipschitzExtensionUp
  deriving DecidableEq

end BEDC.Derived
