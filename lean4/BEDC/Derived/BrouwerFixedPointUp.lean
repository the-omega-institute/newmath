import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive BrouwerFixedPointUp : Type where
  | mk (K S D L W E H C P N : BHist) : BrouwerFixedPointUp
  deriving DecidableEq

end BEDC.Derived
