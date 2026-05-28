import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure EffectiveCompletionUp where
  E : BHist
  Q : BHist
  K : BHist
  W : BHist
  R : BHist
  D : BHist
  A : BHist
  U : BHist
  H : BHist
  C : BHist
  P : BHist
  N : BHist
  deriving DecidableEq

end BEDC.Derived
