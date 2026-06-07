import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyStabilityModulusUp : Type where
  | mk
      (cauchySource dyadicTolerance regularWindow streamObservation transport replay
        provenance localCert : BHist) :
      CauchyStabilityModulusUp
  deriving DecidableEq

end BEDC.Derived
