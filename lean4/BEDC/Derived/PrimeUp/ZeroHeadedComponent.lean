import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NatMul_zero_headed_component_absurd {d q n : BHist} :
    NatMul d q n ->
      ((∃ z : BHist, d = BHist.e0 z) ∨ (∃ z : BHist, q = BHist.e0 z) ∨
        (∃ z : BHist, n = BHist.e0 z)) -> False := by
  intro mul zeroComponent
  have dUnary : UnaryHistory d := NatMul_left_unary mul
  have qUnary : UnaryHistory q := NatMul_right_unary mul
  have nUnary : UnaryHistory n := NatMul_result_unary dUnary mul
  cases zeroComponent with
  | inl dZero =>
      cases dZero with
      | intro z dEq =>
          cases dEq
          exact unary_no_zero_extension dUnary
  | inr rest =>
      cases rest with
      | inl qZero =>
          cases qZero with
          | intro z qEq =>
              cases qEq
              exact unary_no_zero_extension qUnary
      | inr nZero =>
          cases nZero with
          | intro z nEq =>
              cases nEq
              exact unary_no_zero_extension nUnary

theorem NatDivides_zero_headed_component_absurd {d n : BHist} :
    NatDivides d n -> ((∃ z : BHist, d = BHist.e0 z) ∨
      (∃ z : BHist, n = BHist.e0 z)) -> False := by
  intro divides zeroComponent
  cases divides with
  | intro q qData =>
      exact NatMul_zero_headed_component_absurd qData.right
        (Or.elim zeroComponent
          (fun dZero => Or.inl dZero)
          (fun nZero => Or.inr (Or.inr nZero)))

end BEDC.Derived.PrimeUp
