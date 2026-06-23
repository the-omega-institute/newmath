import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteContractionOrbitErrorUp : Type where
  | mk
      (contraction metric map window dyadicBudget cauchyRoute realSeal transport replay provenance
        localName : BHist) :
      FiniteContractionOrbitErrorUp
  deriving DecidableEq

end BEDC.Derived
