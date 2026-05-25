import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive EffectiveCompletionUp : Type where
  | mk (E Q K W R D A U H C P N : BHist) : EffectiveCompletionUp
  deriving DecidableEq

end BEDC.Derived
