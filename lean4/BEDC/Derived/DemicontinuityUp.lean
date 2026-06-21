import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure DemicontinuityUp : Type where
  banachSource : BHist
  weakInput : BHist
  metricOutput : BHist
  scalarSeal : BHist
  action : BHist
  stability : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  nameCert : BHist
  deriving DecidableEq

end BEDC.Derived
