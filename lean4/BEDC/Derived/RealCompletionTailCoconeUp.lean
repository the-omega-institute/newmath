import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RealCompletionTailCoconeUp : Type where
  | mk (D S Q R U L H C P N : BHist) : RealCompletionTailCoconeUp
  deriving DecidableEq

end BEDC.Derived
