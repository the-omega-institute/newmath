import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure ClosedMetricGraphUp where
  sourceMetric : BHist
  targetMetric : BHist
  graphRow : BHist
  sourceWindow : BHist
  targetWindow : BHist
  regularReadback : BHist
  realSeal : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  localName : BHist

end BEDC.Derived
