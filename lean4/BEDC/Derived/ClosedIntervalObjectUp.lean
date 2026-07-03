import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ClosedIntervalObjectUp : Type where
  | mk (a b O M W D R E H C P N : BHist) : ClosedIntervalObjectUp

end BEDC.Derived
