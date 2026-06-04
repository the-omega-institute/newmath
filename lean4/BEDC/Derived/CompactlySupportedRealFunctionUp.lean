import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompactlySupportedRealFunctionUp : Type where
  | mk : (G R S K H T C P N : BHist) -> CompactlySupportedRealFunctionUp
  deriving DecidableEq

end BEDC.Derived
