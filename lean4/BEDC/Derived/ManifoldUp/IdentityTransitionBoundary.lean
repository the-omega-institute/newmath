import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ManifoldTransitionCoherenceLedger_identity_transition_boundary
    (row : ManifoldTransitionCoherenceLedger) :
    hsame row.chart BHist.Empty ∧ hsame row.domain BHist.Empty ∧
      hsame row.value BHist.Empty ∧ hsame row.selfTransition BHist.Empty ∧
        hsame row.selfTransition (append row.value row.value) ∧
          UnaryHistory row.selfTransition := by
  have chartEmpty : hsame row.chart BHist.Empty := row.chartCarrier
  have domainChart : hsame row.domain row.chart :=
    cont_left_unit_result row.domainReadback
  have domainEmpty : hsame row.domain BHist.Empty :=
    hsame_trans domainChart chartEmpty
  have valueChart : hsame row.value row.chart :=
    cont_right_unit_result row.valueReadback
  have valueEmpty : hsame row.value BHist.Empty :=
    hsame_trans valueChart chartEmpty
  have emptyRow : Cont BHist.Empty BHist.Empty BHist.Empty :=
    cont_left_unit BHist.Empty
  have selfEmpty : hsame row.selfTransition BHist.Empty :=
    cont_respects_hsame valueEmpty valueEmpty row.identityRow emptyRow
  have selfAppend : hsame row.selfTransition (append row.value row.value) :=
    row.identityRow
  have selfUnary : UnaryHistory row.selfTransition :=
    unary_transport unary_empty (hsame_symm selfEmpty)
  exact And.intro chartEmpty
    (And.intro domainEmpty
      (And.intro valueEmpty
        (And.intro selfEmpty (And.intro selfAppend selfUnary))))

end BEDC.Derived.ManifoldUp
