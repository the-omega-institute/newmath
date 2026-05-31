import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompactDiniModulusUp : Type where
  | mk (K F M epsilon L U R E H C P N : BHist) : CompactDiniModulusUp
  deriving DecidableEq

end BEDC.Derived
