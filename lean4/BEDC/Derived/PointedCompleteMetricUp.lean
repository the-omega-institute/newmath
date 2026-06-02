import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure PointedCompleteMetricUp : Type where
  metricSpace : BHist
  completion : BHist
  basePoint : BHist
  rootedCauchy : BHist
  transport : BHist
  replay : BHist
  nameCert : BHist
  deriving DecidableEq

end BEDC.Derived
