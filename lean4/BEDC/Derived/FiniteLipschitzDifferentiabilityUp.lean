import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteLipschitzDifferentiabilityUp : Type where
  | mk (L E D M A H C P N : BHist) : FiniteLipschitzDifferentiabilityUp
  deriving DecidableEq

end BEDC.Derived
