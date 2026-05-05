import BEDC.Derived.PrimeUp.DividesClosure
import BEDC.Derived.PrimeUp.FactorialShape
import BEDC.Derived.PrimeUp.UnitResult

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

theorem NatUnaryStrictPrefix_successor_boundary {d n : BHist} :
    UnaryHistory d -> NatUnaryStrictPrefix d (BHist.e1 n) ->
      hsame d n ∨ NatUnaryStrictPrefix d n := by
  intro dUnary strict
  cases strict with
  | intro tail data =>
      cases data with
      | intro tailUnary strictData =>
          cases strictData with
          | intro tailNonempty tailCont =>
              cases tail with
              | Empty =>
                  exact False.elim (tailNonempty rfl)
              | e0 tail =>
                  exact False.elim (unary_no_zero_extension tailUnary)
              | e1 tail =>
                  cases tail with
                  | Empty =>
                      have sameDN : hsame d n := by
                        cases d with
                        | Empty =>
                            cases tailCont
                            rfl
                        | e0 dTail =>
                            cases dUnary
                        | e1 dTail =>
                            exact (append_empty_right (BHist.e1 dTail)).symm.trans
                              (BHist.e1.inj tailCont).symm
                      exact Or.inl sameDN
                  | e0 tailTail =>
                      exact False.elim (unary_no_zero_extension (unary_e1_inversion tailUnary))
                  | e1 tailTail =>
                      have shorterCont : Cont d (BHist.e1 tailTail) n := by
                        exact cont_intro (BHist.e1.inj tailCont)
                      exact Or.inr
                        ⟨BHist.e1 tailTail, unary_e1_inversion tailUnary,
                          (fun empty => by cases empty), shorterCont⟩

theorem NatFact_bounded_positive_predecessor_divides {n m d : BHist} :
    NatFact n m -> UnaryHistory d -> NatUnaryStrictPrefix BHist.Empty d ->
      (hsame d n ∨ NatUnaryStrictPrefix d n) -> NatDivides d m := by
  intro fact
  induction fact generalizing d with
  | zero =>
      intro dUnary dPositive bounded
      cases bounded with
      | inl sameD =>
          cases sameD
          exact False.elim (NatUnaryStrictPrefix_empty_right_absurd dPositive)
      | inr strictD =>
          exact False.elim (NatUnaryStrictPrefix_empty_right_absurd strictD)
  | succ previous mul ih =>
      intro dUnary dPositive bounded
      cases bounded with
      | inl sameEndpoint =>
          have endpointDivides : NatDivides (BHist.e1 _) _ :=
            NatFact_successor_input_divides_result (NatFact.succ previous mul)
          exact (NatDivides_divisor_hsame_transport endpointDivides (hsame_symm sameEndpoint)).right
      | inr strictEndpoint =>
          have predecessorBounded :
              hsame d _ ∨ NatUnaryStrictPrefix d _ :=
            NatUnaryStrictPrefix_successor_boundary dUnary strictEndpoint
          have dividesPrevious : NatDivides d _ := ih dUnary dPositive predecessorBounded
          exact NatDivides_mul_left_closed (unary_e1_closed (NatFact_input_unary previous))
            dividesPrevious mul

theorem NatFact_successor_no_bounded_nonunit_divisor {n m d : BHist} :
    NatFact n m -> UnaryHistory d -> NatUnaryStrictPrefix BHist.Empty d ->
      (hsame d (BHist.e1 BHist.Empty) -> False) ->
        (NatUnaryStrictPrefix d n ∨ hsame d n) ->
          NatDivides d (BHist.e1 m) -> False := by
  intro fact dUnary dPositive dNonunit bounded dividesSucc
  have dNonempty : hsame d BHist.Empty -> False := by
    intro dEmpty
    cases dEmpty
    exact NatUnaryStrictPrefix_empty_right_absurd dPositive
  have boundedForAbsorption : hsame d n ∨ NatUnaryStrictPrefix d n := by
    cases bounded with
    | inl strict =>
        exact Or.inr strict
    | inr same =>
        exact Or.inl same
  have dividesResult : NatDivides d m :=
    NatFact_bounded_positive_predecessor_divides fact dUnary dPositive boundedForAbsorption
  have unitDivides : NatDivides d (BHist.e1 BHist.Empty) :=
    NatDivides_prefix_cancellation dUnary dNonempty (NatFact_result_unary fact)
      (unary_e1_closed unary_empty) (NatDivides_result_unary dividesSucc) (cont_intro rfl)
      dividesResult dividesSucc
  exact dNonunit (Iff.mp NatDivides_unit_right_iff unitDivides)

end BEDC.Derived.PrimeUp
