import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ConstructiveLocatedRealUp : Type where
  | mk (D S R E A F H C P N : BHist) : ConstructiveLocatedRealUp
  deriving DecidableEq

end BEDC.Derived
