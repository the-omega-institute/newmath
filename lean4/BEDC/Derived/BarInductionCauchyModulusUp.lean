import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BarInductionCauchyModulusUp : Type where
  | mk (bar fan window readback tolerance realSeal transport replay provenance nameCert : BHist) :
      BarInductionCauchyModulusUp
  deriving DecidableEq

end BEDC.Derived
