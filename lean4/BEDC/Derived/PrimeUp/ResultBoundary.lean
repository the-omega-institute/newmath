import BEDC.Derived.PrimeUp

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

theorem NatDivides_nonempty_result_boundary {d n : BHist} :
    NatDivides d n -> UnaryHistory n -> (hsame n BHist.Empty -> False) ->
      hsame d n ∨ NatUnaryStrictPrefix d n := by
  intro divides _nUnary nNonempty
  cases divides with
  | intro q qData =>
      cases qData with
      | intro qUnary mul =>
          cases q with
          | Empty =>
              cases mul with
              | zero _dUnary =>
                  exact False.elim (nNonempty rfl)
          | e0 _q =>
              cases qUnary
          | e1 qTail =>
              cases qTail with
              | Empty =>
                  exact Or.inl (hsame_symm (NatMul_unit_right_hsame mul))
              | e0 _q =>
                  cases qUnary
              | e1 _q =>
                  cases mul with
                  | succ previous step =>
                      have dUnary : UnaryHistory d := NatMul_left_unary previous
                      have predUnary := NatMul_result_unary dUnary previous
                      refine Or.inr ⟨_, predUnary, ?_, ?_⟩
                      · intro predEmpty
                        have dEmpty : hsame d BHist.Empty :=
                          NatMul_succ_result_empty_left_empty previous predEmpty
                        cases dEmpty
                        cases predEmpty
                        exact nNonempty step
                      · exact cont_intro (step.trans (unary_append_comm predUnary dUnary))

end BEDC.Derived.PrimeUp
