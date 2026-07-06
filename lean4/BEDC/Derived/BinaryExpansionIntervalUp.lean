import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BinaryExpansionIntervalUp : Type where
  | mk
      (lowerPrefix upperPrefix endpointNormalization dyadicEnclosure streamWindow regSeqReadback
        realSeal transport replay provenance localNameCert : BHist) :
      BinaryExpansionIntervalUp
  deriving DecidableEq

end BEDC.Derived
