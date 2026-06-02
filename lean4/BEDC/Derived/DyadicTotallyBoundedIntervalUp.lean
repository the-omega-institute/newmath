import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicTotallyBoundedIntervalUp : Type where
  | mk (L U M Z rho F S R E H C P N : BHist) : DyadicTotallyBoundedIntervalUp
  deriving DecidableEq

end BEDC.Derived
