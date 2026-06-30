import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DyadicToleranceCompositionUp : Type where
  | mk (Q S0 S1 B0 B1 Qp W0 W1 R0 R1 D E H C P N : BHist) :
      DyadicToleranceCompositionUp
  deriving DecidableEq

end BEDC.Derived
