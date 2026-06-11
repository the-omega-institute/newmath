import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive EffectiveRegularRealExtensionalityUp : Type where
  | mk
      (R0 R1 S0 S1 D0 D1 W0 W1 A0 A1 H C P N : BHist) :
      EffectiveRegularRealExtensionalityUp

end BEDC.Derived
