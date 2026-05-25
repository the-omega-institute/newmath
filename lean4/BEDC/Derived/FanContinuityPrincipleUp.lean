import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FanContinuityPrincipleUp : Type where
  | mk (B A Q S R E H C P N : BHist) : FanContinuityPrincipleUp
  deriving DecidableEq

end BEDC.Derived
