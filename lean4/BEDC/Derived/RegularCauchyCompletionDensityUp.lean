import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyCompletionDensityUp : Type where
  | mk (D S R Q E H C P N : BHist) : RegularCauchyCompletionDensityUp
  deriving DecidableEq

def regularCauchyCompletionDensityCarrierRows :
    RegularCauchyCompletionDensityUp → List BHist
  | RegularCauchyCompletionDensityUp.mk D S R Q E H C P N =>
      [D, S, R, Q, E, H, C, P, N]

end BEDC.Derived
