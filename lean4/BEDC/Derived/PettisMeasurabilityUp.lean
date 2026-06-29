import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive PettisMeasurabilityUp : Type where
  | mk
      (measureSource banachEndpoint weakScalar separableRange simpleApproximation
        bochnerHandoff dunfordHandoff refusal transport replay provenance localNameCert : BHist) :
      PettisMeasurabilityUp
  deriving DecidableEq

end BEDC.Derived
