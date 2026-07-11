import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LebesgueNumberMeshUp : Type where
  | mk
      (compactMetricSource finiteCoverMesh compactNet localRadiusLedger ratLowerBoundFold
        meshRefinement uniformModulusHandoff transport replay provenance localNameCert : BHist) :
      LebesgueNumberMeshUp
  deriving DecidableEq

end BEDC.Derived
