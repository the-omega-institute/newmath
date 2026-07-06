import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ConstructiveEpigraphProjectionUp : Type where
  | mk
      (epigraph lowerSemicontinuous metric locatedReal realSeal transport replay provenance
        name : BHist) :
      ConstructiveEpigraphProjectionUp
  deriving DecidableEq

end BEDC.Derived
