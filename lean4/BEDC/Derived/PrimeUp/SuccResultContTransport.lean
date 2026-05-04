import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem NatMul_succ_result_cont_transport {d q n n' : BHist} :
    NatMul d (BHist.e1 q) n -> hsame n n' ->
      exists p : BHist, NatMul d q p /\ Cont p d n' := by
  intro mul sameResult
  cases NatMul_succ_inversion mul with
  | intro p step =>
      exact Exists.intro p
        (And.intro step.left (cont_result_hsame_transport step.right sameResult))

end BEDC.Derived.PrimeUp
