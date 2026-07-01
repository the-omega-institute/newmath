import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteCoverMeshUp : Type where
  | mk
      (compactMetricRow totallyBoundedRow metricSpaceRow realSeal regSeqRatReadback
        dyadicTolerance finiteMeshLedger compactHandoff transport replay provenance
        localNameCert : BHist) :
      FiniteCoverMeshUp
  deriving DecidableEq

end BEDC.Derived
