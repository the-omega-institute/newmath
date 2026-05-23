import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicShrinkScheduleUp : Type where
  | mk : (k k' D W R E H C P N : BHist) -> DyadicShrinkScheduleUp
  deriving DecidableEq

end BEDC.Derived
