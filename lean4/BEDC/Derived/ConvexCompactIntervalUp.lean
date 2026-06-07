import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ConvexCompactIntervalUp : Type where
  | mk : (I L F M R E W H C P N : BHist) → ConvexCompactIntervalUp
  deriving DecidableEq

end BEDC.Derived
