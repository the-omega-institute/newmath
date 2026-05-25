import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchySpeedupUp : Type where
  | mk (A J D W R E H C P N : BHist) : CauchySpeedupUp
  deriving DecidableEq

end BEDC.Derived
