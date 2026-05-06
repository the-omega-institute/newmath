import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ManifoldTransitionCoherenceLedger_identity_transition
    (row : ManifoldTransitionCoherenceLedger) :
    hsame row.selfTransition BHist.Empty ∧ hsame row.selfTransition row.value ∧
      UnaryHistory row.value ∧ UnaryHistory row.selfTransition := by
  have valueEmpty : hsame row.value BHist.Empty := by
    have valueChart : hsame row.value row.chart :=
      cont_right_unit_result row.valueReadback
    exact hsame_trans valueChart row.chartCarrier
  have selfEmpty : hsame row.selfTransition BHist.Empty :=
    cont_respects_hsame valueEmpty valueEmpty row.identityRow (cont_left_unit BHist.Empty)
  have selfValue : hsame row.selfTransition row.value :=
    hsame_trans selfEmpty (hsame_symm valueEmpty)
  have valueUnary : UnaryHistory row.value :=
    unary_transport unary_empty (hsame_symm valueEmpty)
  have selfUnary : UnaryHistory row.selfTransition :=
    unary_transport unary_empty (hsame_symm selfEmpty)
  exact And.intro selfEmpty (And.intro selfValue (And.intro valueUnary selfUnary))

theorem ManifoldTransitionCoherenceLedger_singleton_exhaustion
    (row : ManifoldTransitionCoherenceLedger) :
    hsame row.domain BHist.Empty ∧ hsame row.value BHist.Empty ∧
      hsame row.selfTransition BHist.Empty ∧ hsame row.inverseRound BHist.Empty ∧
        hsame row.cocycle BHist.Empty ∧ UnaryHistory row.domain ∧ UnaryHistory row.value ∧
          UnaryHistory row.selfTransition ∧ UnaryHistory row.inverseRound ∧
            UnaryHistory row.cocycle := by
  have domainEmpty : hsame row.domain BHist.Empty := by
    have domainChart : hsame row.domain row.chart :=
      cont_left_unit_result row.domainReadback
    exact hsame_trans domainChart row.chartCarrier
  have valueEmpty : hsame row.value BHist.Empty := by
    have valueChart : hsame row.value row.chart :=
      cont_right_unit_result row.valueReadback
    exact hsame_trans valueChart row.chartCarrier
  have selfEmpty : hsame row.selfTransition BHist.Empty :=
    cont_respects_hsame valueEmpty valueEmpty row.identityRow (cont_left_unit BHist.Empty)
  have inverseEmpty : hsame row.inverseRound BHist.Empty :=
    cont_respects_hsame selfEmpty selfEmpty row.inverseRoundRow (cont_left_unit BHist.Empty)
  have cocycleEmpty : hsame row.cocycle BHist.Empty :=
    cont_respects_hsame inverseEmpty valueEmpty row.cocycleRow (cont_left_unit BHist.Empty)
  have domainUnary : UnaryHistory row.domain :=
    unary_transport unary_empty (hsame_symm domainEmpty)
  have valueUnary : UnaryHistory row.value :=
    unary_transport unary_empty (hsame_symm valueEmpty)
  have selfUnary : UnaryHistory row.selfTransition :=
    unary_transport unary_empty (hsame_symm selfEmpty)
  have inverseUnary : UnaryHistory row.inverseRound :=
    unary_transport unary_empty (hsame_symm inverseEmpty)
  have cocycleUnary : UnaryHistory row.cocycle :=
    unary_transport unary_empty (hsame_symm cocycleEmpty)
  exact And.intro domainEmpty
    (And.intro valueEmpty
      (And.intro selfEmpty
        (And.intro inverseEmpty
          (And.intro cocycleEmpty
            (And.intro domainUnary
              (And.intro valueUnary
                (And.intro selfUnary (And.intro inverseUnary cocycleUnary))))))))

end BEDC.Derived.ManifoldUp
