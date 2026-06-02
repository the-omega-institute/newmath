import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteWindowRegSeqRatHandoffUp : Type where
  | mk
      (window tolerance readback realSeal transport replay provenance name : BHist) :
      FiniteWindowRegSeqRatHandoffUp
  deriving DecidableEq

end BEDC.Derived
