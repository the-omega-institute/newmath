import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RealCompletenessDensityWindowUp : Type where
  | mk (V D S R Q E H C P N : BHist) : RealCompletenessDensityWindowUp
  deriving DecidableEq

def realCompletenessDensityWindowCarrierRows :
    RealCompletenessDensityWindowUp → List BHist
  | RealCompletenessDensityWindowUp.mk V D S R Q E H C P N =>
      [V, D, S, R, Q, E, H, C, P, N]

end BEDC.Derived
