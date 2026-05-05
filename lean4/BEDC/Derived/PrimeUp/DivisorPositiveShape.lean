import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NatDivides_nonempty_result_divisor_positive_shape {d n : BHist} :
    NatDivides d n -> UnaryHistory n -> (hsame n BHist.Empty -> False) ->
      exists tail : BHist, hsame d (BHist.e1 tail) /\ UnaryHistory tail := by
  intro divides _nCarrier nNonempty
  have dCarrier : UnaryHistory d := by
    cases divides with
    | intro _q qData =>
        exact NatMul_left_unary qData.right
  cases d with
  | Empty =>
      exact False.elim (nNonempty (NatDivides_empty_left_result_empty divides))
  | e0 _tail =>
      cases dCarrier
  | e1 tail =>
      exact ⟨tail, hsame_refl (BHist.e1 tail), unary_e1_inversion dCarrier⟩

end BEDC.Derived.PrimeUp
