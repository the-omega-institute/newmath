import BEDC.FKernel.Hist

namespace BEDC.Derived.RefutationGateUp

open BEDC.FKernel.Hist

inductive RefutationGateUp : Type where
  | mk (Q S B A D T H C P N : BHist) : RefutationGateUp
  deriving DecidableEq

end BEDC.Derived.RefutationGateUp
