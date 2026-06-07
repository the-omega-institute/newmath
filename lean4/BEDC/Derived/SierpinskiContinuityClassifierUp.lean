import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SierpinskiContinuityClassifierUp : Type where
  | mk (X Y F O S W H C P N : BHist) : SierpinskiContinuityClassifierUp
  deriving DecidableEq

end BEDC.Derived
