import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyRegularExtractionUp : Type where
  | mk
      (cauchyWitness dyadicLedger window regularReadback extractionWitness transport replay
        provenance localCert : BHist) :
      CauchyRegularExtractionUp
  deriving DecidableEq

end BEDC.Derived
