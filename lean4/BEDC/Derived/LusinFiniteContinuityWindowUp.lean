import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive LusinFiniteContinuityWindowUp : Type where
  | mk (M L C E R S H Q P N : BHist) : LusinFiniteContinuityWindowUp
  deriving DecidableEq

end BEDC.Derived
