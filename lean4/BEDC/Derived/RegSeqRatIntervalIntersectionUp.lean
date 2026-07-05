import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegSeqRatIntervalIntersectionUp : Type where
  | mk (L R W D M S E H C P N : BHist) : RegSeqRatIntervalIntersectionUp
  deriving DecidableEq

end BEDC.Derived
