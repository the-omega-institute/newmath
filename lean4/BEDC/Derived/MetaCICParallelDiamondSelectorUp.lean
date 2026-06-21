import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure MetaCICParallelDiamondSelectorUp : Type where
  typedClosedWindow : BHist
  residualPairFrontier : BHist
  closedParallelDiamondCandidate : BHist
  residualSubstitutionCompatibility : BHist
  selectorLedger : BHist
  obstructionRetention : BHist
  tasteGateRoute : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  nameCert : BHist
  deriving DecidableEq

end BEDC.Derived
