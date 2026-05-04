import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NatFact_result_positive_shape {n m : BHist} :
    NatFact n m -> exists tail : BHist, hsame m (BHist.e1 tail) /\ UnaryHistory tail := by
  intro fact
  have resultUnary : UnaryHistory m := NatFact_result_unary fact
  have resultNonempty : hsame m BHist.Empty -> False := NatFact_result_not_empty fact
  cases m with
  | Empty =>
      exact False.elim (resultNonempty (hsame_refl BHist.Empty))
  | e0 tail =>
      cases resultUnary
  | e1 tail =>
      exact ⟨tail, hsame_refl (BHist.e1 tail), unary_e1_inversion resultUnary⟩

end BEDC.Derived.PrimeUp
