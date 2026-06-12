import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DedekindCutBoundaryUp : Type where
  | mk
      (locatedCut dedekindReal comparison regularReadback streamWindow dyadicTolerance realSeal
        transport replay provenance name : BHist) :
      DedekindCutBoundaryUp
  deriving DecidableEq

end BEDC.Derived
