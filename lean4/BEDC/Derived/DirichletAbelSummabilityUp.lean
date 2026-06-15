import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DirichletAbelSummabilityUp : Type where
  | mk
      (source abelFace dirichletFace uniformHandoff readback realSeal transport replay
        provenance localName : BHist) :
      DirichletAbelSummabilityUp
  deriving DecidableEq

def dirichletAbelSummabilityRows : DirichletAbelSummabilityUp -> List BHist
  | DirichletAbelSummabilityUp.mk S A D U R E H C P N => [S, A, D, U, R, E, H, C, P, N]

end BEDC.Derived
