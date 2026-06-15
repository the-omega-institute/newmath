import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyReciprocalModulusUp : Type where
  | mk (S D A K R E H C P N : BHist) : RegularCauchyReciprocalModulusUp
  deriving DecidableEq

end BEDC.Derived
