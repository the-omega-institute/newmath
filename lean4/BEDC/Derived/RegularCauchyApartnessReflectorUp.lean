import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyApartnessReflectorUp : Type where
  | mk (S R D A L E H C N : BHist) : RegularCauchyApartnessReflectorUp
  deriving DecidableEq

end BEDC.Derived
