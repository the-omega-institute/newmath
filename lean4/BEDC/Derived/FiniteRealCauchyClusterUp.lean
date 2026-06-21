import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive FiniteRealCauchyClusterUp : Type where
  | mk (S R D L E H C P N : BHist) : FiniteRealCauchyClusterUp

end BEDC.Derived
