import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyRateRealizationUp : Type where
  | mk : (p r d s q m e H C P N : BHist) -> CauchyRateRealizationUp
  deriving DecidableEq

end BEDC.Derived
