import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive RegularCauchyTailCollapseUp : Type where
  | mk (R S D W Q U E H C P N : _root_.BEDC.FKernel.Hist.BHist) :
      RegularCauchyTailCollapseUp

end BEDC.Derived
