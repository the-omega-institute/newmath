import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LowerUpperRealCutUp : Type where
  | mk (L U G D S R E H C P N : BHist) : LowerUpperRealCutUp
  deriving DecidableEq

end BEDC.Derived
