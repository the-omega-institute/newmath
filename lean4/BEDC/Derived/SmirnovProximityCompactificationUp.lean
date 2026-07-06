import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SmirnovProximityCompactificationUp : Type where
  | mk (X D U K W R E H C P N : BHist) : SmirnovProximityCompactificationUp
  deriving DecidableEq

end BEDC.Derived
