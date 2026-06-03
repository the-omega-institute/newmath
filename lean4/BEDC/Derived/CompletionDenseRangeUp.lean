import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure CompletionDenseRangeUp where
  S : BHist
  D : BHist
  E : BHist
  U : BHist
  W : BHist
  R : BHist
  Q : BHist
  H : BHist
  C : BHist
  P : BHist
  N : BHist
  deriving DecidableEq

end BEDC.Derived
