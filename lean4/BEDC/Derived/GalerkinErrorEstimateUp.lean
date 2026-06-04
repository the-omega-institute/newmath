import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive GalerkinErrorEstimateUp : Type where
  | mk
      (trial bilinear load exact variational error coercivity continuity comparison transport
        realBound replay provenance localName : BHist) : GalerkinErrorEstimateUp
  deriving DecidableEq

end BEDC.Derived
