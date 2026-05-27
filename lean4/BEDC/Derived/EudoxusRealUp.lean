import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive EudoxusRealUp : Type where
  | mk (I A B D S Q R H C P N : BHist) : EudoxusRealUp
  deriving DecidableEq

end BEDC.Derived
