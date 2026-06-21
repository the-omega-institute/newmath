import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BishopCutUp : Type where
  | mk
      (locatedCut lowerUpperEnvelope envelopeConsistency dyadicTolerance streamWindow
        regularReadback realSeal transport replay provenance localNameCert : BHist) :
      BishopCutUp
  deriving DecidableEq

end BEDC.Derived
