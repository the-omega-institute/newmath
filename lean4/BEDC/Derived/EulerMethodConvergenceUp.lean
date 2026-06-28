import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure EulerMethodConvergenceUp : Type where
  step : BHist
  gronwall : BHist
  window : BHist
  readback : BHist
  dyadic : BHist
  realSeal : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  namecert : BHist

end BEDC.Derived
