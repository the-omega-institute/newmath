import BEDC.Derived.PrimeUp.FactorialAbsorption
import BEDC.Derived.PrimeUp.ResultBoundary

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

private theorem NatUnary_nonempty_positive {d : BHist} :
    UnaryHistory d -> (hsame d BHist.Empty -> False) -> NatUnaryStrictPrefix BHist.Empty d := by
  intro dUnary dNonempty
  cases d with
  | Empty =>
      exact False.elim (dNonempty rfl)
  | e0 dTail =>
      cases dUnary
  | e1 dTail =>
      exact ⟨BHist.e1 dTail, dUnary, (fun empty => by cases empty), cont_left_unit _⟩

private theorem NatUnaryStrictPrefix_hsame_target_transport {d b b' : BHist} :
    NatUnaryStrictPrefix d b -> hsame b b' -> NatUnaryStrictPrefix d b' := by
  intro strict sameTarget
  cases strict with
  | intro tail data =>
      exact NatUnaryStrictPrefix_cont_hsame_transport data.left data.right.left data.right.right
        (hsame_refl d) sameTarget

private theorem TrialDiv_strict_prefix_divisor_screened {b n d : BHist} :
    TrialDiv b n -> UnaryHistory d -> NatDivides d n ->
      NatUnaryStrictPrefix BHist.Empty d -> NatUnaryStrictPrefix d b ->
        hsame d (BHist.e1 BHist.Empty) ∨ hsame d n := by
  intro trial
  induction trial generalizing d with
  | unit hn =>
      intro dUnary _divides dPositive strictUnit
      have boundary := NatUnaryStrictPrefix_successor_boundary dUnary strictUnit
      cases boundary with
      | inl dEmpty =>
          cases dEmpty
          exact False.elim (NatUnaryStrictPrefix_empty_right_absurd dPositive)
      | inr strictEmpty =>
          exact False.elim (NatUnaryStrictPrefix_empty_right_absurd strictEmpty)
  | step previous advance stepCont ih =>
      intro dUnary divides dPositive strictCurrent
      have currentSucc : hsame _ (BHist.e1 _) :=
        stepCont.trans (congrArg BHist.e1 (append_empty_right _))
      have strictSucc : NatUnaryStrictPrefix d (BHist.e1 _) :=
        NatUnaryStrictPrefix_hsame_target_transport strictCurrent currentSucc
      have boundary := NatUnaryStrictPrefix_successor_boundary dUnary strictSucc
      cases boundary with
      | inl samePrevious =>
          have previousDivides : NatDivides _ _ :=
            (NatDivides_divisor_hsame_transport divides samePrevious).right
          cases advance with
          | inl previousExcluded =>
              exact False.elim (previousExcluded previousDivides)
          | inr endpoint =>
              cases endpoint with
              | inl previousUnit =>
                  exact Or.inl (hsame_trans samePrevious previousUnit)
              | inr previousTarget =>
                  exact Or.inr (hsame_trans samePrevious previousTarget)
      | inr strictPrevious =>
          exact ih dUnary divides dPositive strictPrevious

theorem TrialDiv_terminal_excludes_nontrivial_divisors {n d : BHist} :
    UnaryHistory n -> NatUnaryStrictPrefix (BHist.e1 BHist.Empty) n -> TrialDiv n n ->
      UnaryHistory d -> NatDivides d n ->
        hsame d (BHist.e1 BHist.Empty) ∨ hsame d n := by
  intro nUnary nPositive trial dUnary divides
  have nNonempty : hsame n BHist.Empty -> False := by
    intro nEmpty
    cases nEmpty
    exact NatUnaryStrictPrefix_empty_right_absurd nPositive
  have boundary := NatDivides_nonempty_result_boundary divides nUnary nNonempty
  cases boundary with
  | inl sameDN =>
      exact Or.inr sameDN
  | inr strictDN =>
      have dNonempty : hsame d BHist.Empty -> False := by
        intro dEmpty
        cases dEmpty
        exact nNonempty (NatDivides_empty_left_result_empty divides)
      have dPositive := NatUnary_nonempty_positive dUnary dNonempty
      exact TrialDiv_strict_prefix_divisor_screened trial dUnary divides dPositive strictDN

end BEDC.Derived.PrimeUp
