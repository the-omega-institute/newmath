import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive MonotoneBarModulusUp : Type where
  | mk (T B D W R E H C P N : BHist) : MonotoneBarModulusUp
  deriving DecidableEq

end BEDC.Derived
