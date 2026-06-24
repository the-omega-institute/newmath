import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyCompletionModulusRealizerUp : Type where
  | mk (Q W D M K B E H C P N : BHist) : RegularCauchyCompletionModulusRealizerUp
  deriving DecidableEq

end BEDC.Derived
