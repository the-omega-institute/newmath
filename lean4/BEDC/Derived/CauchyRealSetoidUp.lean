import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyRealSetoidUp : Type where
  | mk (L R W D M Q E H C P N : BHist) : CauchyRealSetoidUp
  deriving DecidableEq

end BEDC.Derived
