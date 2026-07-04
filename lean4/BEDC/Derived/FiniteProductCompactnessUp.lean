import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteProductCompactnessUp : Type where
  | mk
      (indexSpine compactComponents productTopology productNet dyadicRadius realReadback
        transport replay provenance localNameCert : BHist) :
      FiniteProductCompactnessUp
  deriving DecidableEq

end BEDC.Derived
