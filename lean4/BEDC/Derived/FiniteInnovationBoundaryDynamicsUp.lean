import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteInnovationBoundaryDynamicsUp : Type where
  | mk
      (gaussBranchRows mayerTransferRows regulatorRows numericalCongruenceRows
        reflectionObstructionRows transport replay provenance localNameCert : BHist) :
      FiniteInnovationBoundaryDynamicsUp
  deriving DecidableEq

end BEDC.Derived
