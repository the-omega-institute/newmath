import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LocatedDyadicCutUp : Type where
  | mk (L U G D S R E H C P N : BHist) : LocatedDyadicCutUp
  deriving DecidableEq

end BEDC.Derived
