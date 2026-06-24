import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive AumannIntegralUp : Type where
  | mk (M R X F G S K I B H C P N : BHist) : AumannIntegralUp
  deriving DecidableEq

end BEDC.Derived
