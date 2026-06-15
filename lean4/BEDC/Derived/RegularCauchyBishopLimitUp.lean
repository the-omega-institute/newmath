import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyBishopLimitUp : Type where
  | mk (S W D R E H C P N : BHist) : RegularCauchyBishopLimitUp
  deriving DecidableEq

end BEDC.Derived
