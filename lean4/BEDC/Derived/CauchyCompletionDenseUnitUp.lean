import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyCompletionDenseUnitUp : Type where
  | mk (X U D A R H C P N : BHist) : CauchyCompletionDenseUnitUp
  deriving DecidableEq

end BEDC.Derived
