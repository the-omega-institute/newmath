import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FabryGapTheoremUp : Type where
  | mk
      (gapLedger coefficientWindow radiusRow rootTestHandoff boundaryProbe witnessWindow
        exclusionRow transport replay provenance localNameCert : BHist) :
      FabryGapTheoremUp
  deriving DecidableEq

end BEDC.Derived
