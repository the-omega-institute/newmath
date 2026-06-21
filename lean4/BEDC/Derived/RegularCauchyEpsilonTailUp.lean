import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyEpsilonTailUp : Type where
  | mk (S R D Q T H C P N : BHist) : RegularCauchyEpsilonTailUp

end BEDC.Derived
