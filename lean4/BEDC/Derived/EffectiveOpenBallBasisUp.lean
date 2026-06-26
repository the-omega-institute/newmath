import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive EffectiveOpenBallBasisUp : Type where
  | mk
      (metricSource centerSchedule radiusLedger streamWindows regularReadback realSeal
        topologyHandoff transport replay provenance localNameCert : BHist) :
      EffectiveOpenBallBasisUp
  deriving DecidableEq

end BEDC.Derived
