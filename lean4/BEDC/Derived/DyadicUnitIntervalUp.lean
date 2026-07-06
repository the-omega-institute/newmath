import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicUnitIntervalUp : Type where
  | mk (L R I F S Q E H C P N : BHist) : DyadicUnitIntervalUp
  deriving DecidableEq

end BEDC.Derived
