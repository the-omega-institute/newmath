import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyModulusChoiceUp : Type where
  | mk (M N W Q D R H C P L : BHist) : CauchyModulusChoiceUp

end BEDC.Derived
