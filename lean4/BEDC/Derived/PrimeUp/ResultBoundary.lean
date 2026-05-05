import BEDC.Derived.PrimeUp
import BEDC.Derived.PrimeUp.NatMulTransport

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

theorem NatDivides_antisymmetry_hsame {d e : BHist} :
    UnaryHistory d -> UnaryHistory e -> NatDivides d e -> NatDivides e d -> hsame d e := by
  intro dUnary eUnary dividesDE dividesED
  cases d with
  | Empty =>
      exact hsame_symm (NatDivides_empty_left_result_empty dividesDE)
  | e0 _ =>
      cases dUnary
  | e1 dTail =>
      cases e with
      | Empty =>
          exact NatDivides_empty_left_result_empty dividesED
      | e0 _ =>
          cases eUnary
      | e1 eTail =>
          have dNonempty : hsame (BHist.e1 dTail) BHist.Empty -> False := by
            intro same
            exact not_hsame_e1_empty same
          have eNonempty : hsame (BHist.e1 eTail) BHist.Empty -> False := by
            intro same
            exact not_hsame_e1_empty same
          cases NatDivides_nonempty_result_boundary dividesDE eUnary eNonempty with
          | inl sameDE =>
              exact sameDE
          | inr strictDE =>
              cases NatDivides_nonempty_result_boundary dividesED dUnary dNonempty with
              | inl sameED =>
                  exact hsame_symm sameED
              | inr strictED =>
                  exact False.elim (NatUnaryStrictPrefix_asymm strictDE strictED)

theorem NatMul_succ_result_eq_factor_empty_or_multiplier_empty {d q n : BHist} :
    UnaryHistory d -> NatMul d (BHist.e1 q) n -> hsame n d ->
      hsame d BHist.Empty ∨ hsame q BHist.Empty := by
  intro _dUnary mul sameResult
  cases NatMul_succ_inversion mul with
  | intro p step =>
      have displayed : Cont p d d := cont_result_hsame_transport step.right sameResult
      have unitDisplayed : Cont BHist.Empty d d := cont_intro (append_empty_left d).symm
      have pEmpty : hsame p BHist.Empty := cont_right_cancel displayed unitDisplayed
      have emptyProduct : NatMul d q BHist.Empty :=
        (NatMul_result_hsame_transport step.left pEmpty).right
      exact NatMul_empty_result_factor_empty_or_multiplier_empty emptyProduct

theorem NatPrime_NatMul_nonunit_factor_multiplier_unit {p d q : BHist} :
    NatPrime p -> UnaryHistory d -> UnaryHistory q -> NatMul d q p ->
      (hsame d (BHist.e1 BHist.Empty) -> False) ->
        hsame d p ∧ hsame q (BHist.e1 BHist.Empty) := by
  intro prime dUnary qUnary mul dNonunit
  have divides : NatDivides d p := Exists.intro q (And.intro qUnary mul)
  have divisorBoundary := prime.right.right d dUnary divides
  have sameDP : hsame d p := by
    cases divisorBoundary with
    | inl dUnit =>
        exact False.elim (dNonunit dUnit)
    | inr dPrime =>
        exact dPrime
  constructor
  · exact sameDP
  · cases q with
    | Empty =>
        cases mul
        exact False.elim (NatUnaryStrictPrefix_empty_right_absurd prime.right.left)
    | e0 qTail =>
        cases qUnary
    | e1 qTail =>
        have boundary :=
          NatMul_succ_result_eq_factor_empty_or_multiplier_empty dUnary mul (hsame_symm sameDP)
        cases boundary with
        | inl dEmpty =>
            cases dEmpty
            cases sameDP
            exact False.elim (NatUnaryStrictPrefix_empty_right_absurd prime.right.left)
        | inr qTailEmpty =>
            cases qTailEmpty
            rfl

end BEDC.Derived.PrimeUp
