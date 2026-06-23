import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SchurDecompositionUp : Type where
  | mk (source scalarBoundary unitaryLedger triangularLedger diagonalReadback residualExactness
      transport replay provenance name : BHist) : SchurDecompositionUp
  deriving DecidableEq

end BEDC.Derived
