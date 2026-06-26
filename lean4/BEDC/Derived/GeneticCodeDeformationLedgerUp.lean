import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive GeneticCodeDeformationLedgerUp : Type where
  | mk
      (tableRow stopSet senseSet roleUAA roleUAG roleUGA roleUGG boundary standardShape
        symmetricDifference transport replay provenance name : BHist) :
      GeneticCodeDeformationLedgerUp
  deriving DecidableEq

end BEDC.Derived
