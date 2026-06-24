import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BishopDiagonalRegularizationUp : Type where
  | mk
      (modulusChoice streamWindows dyadicTolerances regSeqReadback realSeal
        transport replay provenance localNameCert : BHist) :
      BishopDiagonalRegularizationUp
  deriving DecidableEq

end BEDC.Derived
