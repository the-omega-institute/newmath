import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive ChoiceFreeRealSealUp : Type where
  | mk
      (window regularReadback dyadicTolerance realSeal ledger transport replay provenance name :
        BHist) :
      ChoiceFreeRealSealUp
  deriving DecidableEq

end BEDC.Derived
