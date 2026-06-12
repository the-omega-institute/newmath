import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive WeakCompactnessUp : Type where
  | mk (F T B A C R H Q P N : BHist) : WeakCompactnessUp
  deriving DecidableEq

end BEDC.Derived
