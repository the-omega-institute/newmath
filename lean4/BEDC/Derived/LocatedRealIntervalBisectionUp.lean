import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedRealIntervalBisectionUp : Type where
  | mk (I B M D W R E H C P N : BHist) : LocatedRealIntervalBisectionUp
  deriving DecidableEq

end BEDC.Derived
