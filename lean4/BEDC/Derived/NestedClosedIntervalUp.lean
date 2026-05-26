import BEDC.FKernel.Hist

namespace BEDC.Derived

structure NestedClosedIntervalUp where
  intervalRows : BEDC.FKernel.Hist.BHist
  dyadicLedger : BEDC.FKernel.Hist.BHist
  streamWindow : BEDC.FKernel.Hist.BHist
  regularReadback : BEDC.FKernel.Hist.BHist
  realHandoff : BEDC.FKernel.Hist.BHist

end BEDC.Derived
