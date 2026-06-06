import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive RegularCauchyDiagonalExchangeUp : Type where
  | mk (S D R Q T L H C P N : _root_.BEDC.FKernel.Hist.BHist) :
      RegularCauchyDiagonalExchangeUp

end BEDC.Derived
