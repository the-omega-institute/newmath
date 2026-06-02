import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedLowerBoundUp : Type where
  | mk (F L W R E H C P N : BHist) : LocatedLowerBoundUp
  deriving DecidableEq

end BEDC.Derived
