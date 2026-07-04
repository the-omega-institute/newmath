import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyCommonTailSealUp : Type where
  | mk (L R D W Q E H C P N : BHist) : RegularCauchyCommonTailSealUp

end BEDC.Derived
