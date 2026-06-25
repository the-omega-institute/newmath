import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyUniqueLimitUp : Type where
  | mk (Q Q' W W' D S E H C P N : BHist) : RegularCauchyUniqueLimitUp
  deriving DecidableEq

end BEDC.Derived
