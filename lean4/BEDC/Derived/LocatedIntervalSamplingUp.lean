import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedIntervalSamplingUp : Type where
  | mk (I N W R E H C P L : BHist) : LocatedIntervalSamplingUp
  deriving DecidableEq

end BEDC.Derived
