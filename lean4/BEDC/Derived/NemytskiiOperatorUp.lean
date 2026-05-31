import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive NemytskiiOperatorUp : Type where
  | mk (D M F W I T S R H C P N : BHist) : NemytskiiOperatorUp
  deriving DecidableEq

end BEDC.Derived
