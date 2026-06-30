import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyModulusThinningUp : Type where
  | mk (M T D W R E H C P N : BHist) : CauchyModulusThinningUp

end BEDC.Derived
