import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompactOpenMetricUp : Type where
  | mk (X Y F G M D S H C P N : BHist) : CompactOpenMetricUp
  deriving DecidableEq

end BEDC.Derived
