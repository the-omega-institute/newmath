import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MetaCICResidualDiamondWitnessUp : Type where
  | mk
      (typedWindow residualFrontier localJoinChecker substitutionBoundary obstructionRetention
        transport replay provenance name : BHist) :
      MetaCICResidualDiamondWitnessUp

end BEDC.Derived
