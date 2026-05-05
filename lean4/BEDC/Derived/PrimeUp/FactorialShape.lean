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

theorem NatFact_successor_input_divides_result {n m : BHist} :
    NatFact (BHist.e1 n) m -> NatDivides (BHist.e1 n) m := by
  intro fact
  cases NatFact_successor_inversion fact with
  | intro previous data =>
      exact Exists.intro previous (And.intro (NatFact_result_unary data.left) data.right)

end BEDC.Derived.PrimeUp
