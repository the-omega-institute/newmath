import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyNestedIntervalUp : Type where
  | mk (L U S I D R E H C P N : BHist) : RegularCauchyNestedIntervalUp

end BEDC.Derived
