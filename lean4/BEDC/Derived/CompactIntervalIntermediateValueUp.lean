import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompactIntervalIntermediateValueUp : Type where
  | mk : (I F B D R E H C P N : BHist) → CompactIntervalIntermediateValueUp
  deriving DecidableEq

end BEDC.Derived
