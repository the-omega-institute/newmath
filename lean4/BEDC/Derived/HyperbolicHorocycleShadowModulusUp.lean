import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure HyperbolicHorocycleShadowModulusUp : Type where
  horocycleRow : BHist
  busemannBoundary : BHist
  visualBoundary : BHist
  boundaryShadow : BHist
  shadowBudget : BHist
  hyperbolicMetric : BHist
  realSeal : BHist
  tasteGateRoute : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  nameCert : BHist
  deriving DecidableEq

end BEDC.Derived
