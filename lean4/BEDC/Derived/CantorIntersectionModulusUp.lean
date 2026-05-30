import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CantorIntersectionModulusUp : Type where
  | mk (L B D S R E F H C P N : BHist) : CantorIntersectionModulusUp
  deriving DecidableEq

end BEDC.Derived
