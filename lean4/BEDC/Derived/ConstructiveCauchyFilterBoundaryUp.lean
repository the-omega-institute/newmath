import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ConstructiveCauchyFilterBoundaryUp : Type where
  | mk
      (filter window readback tolerance realSeal transport replay provenance name : BHist) :
      ConstructiveCauchyFilterBoundaryUp
  deriving DecidableEq

end BEDC.Derived
