import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive DirectMethodMinimizerUp : Type where
  | mk (X K L S F M Q E H C P N : BHist) : DirectMethodMinimizerUp
  deriving DecidableEq

end BEDC.Derived
