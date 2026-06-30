import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CourantFischerMinimaxUp : Type where
  | mk
      (matrix operator innerProduct subspaceWindow rayleighLedger minmaxComparison
        extremalLedger transport replay provenance name : BHist) :
      CourantFischerMinimaxUp
  deriving DecidableEq

end BEDC.Derived
