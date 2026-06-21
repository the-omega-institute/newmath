import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteCandidateDiamondUp : Type where
  | mk
      (authorizedGenerator recursorGenerator criticalPath parallelFrontier candidateBoundary
        localJoinLedger tasteGateExpectation transport replay provenance localNameCert : BHist) :
      FiniteCandidateDiamondUp
  deriving DecidableEq

end BEDC.Derived
