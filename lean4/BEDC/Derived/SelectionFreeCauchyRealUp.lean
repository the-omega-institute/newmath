import BEDC.FKernel.Hist

namespace BEDC.Derived

inductive SelectionFreeCauchyRealUp : Type where
  | mk (S R D Q E B H C P N : BEDC.FKernel.Hist.BHist) : SelectionFreeCauchyRealUp
  deriving DecidableEq

end BEDC.Derived
