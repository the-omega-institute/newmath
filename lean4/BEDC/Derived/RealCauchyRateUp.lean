import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RealCauchyRateUp : Type where
  | mk : (D S Q R H C P N : BHist) -> RealCauchyRateUp
  deriving DecidableEq

end BEDC.Derived
