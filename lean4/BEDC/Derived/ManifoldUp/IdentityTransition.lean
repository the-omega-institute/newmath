import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ManifoldTransitionCoherenceLedger_identity_transition_empty
    (L : ManifoldTransitionCoherenceLedger) :
    hsame L.value BHist.Empty ∧ hsame L.selfTransition BHist.Empty ∧
      hsame L.inverseRound BHist.Empty ∧ UnaryHistory L.selfTransition ∧
        UnaryHistory L.inverseRound ∧ Cont L.value L.value L.selfTransition := by
  have valueChart : hsame L.value L.chart :=
    cont_right_unit_result L.valueReadback
  have valueEmpty : hsame L.value BHist.Empty :=
    hsame_trans valueChart L.chartCarrier
  have emptyRow : Cont BHist.Empty BHist.Empty BHist.Empty :=
    cont_left_unit BHist.Empty
  have selfEmpty : hsame L.selfTransition BHist.Empty :=
    cont_respects_hsame valueEmpty valueEmpty L.identityRow emptyRow
  have inverseEmpty : hsame L.inverseRound BHist.Empty :=
    cont_respects_hsame selfEmpty selfEmpty L.inverseRoundRow emptyRow
  have selfUnary : UnaryHistory L.selfTransition :=
    unary_transport unary_empty (hsame_symm selfEmpty)
  have inverseUnary : UnaryHistory L.inverseRound :=
    unary_transport unary_empty (hsame_symm inverseEmpty)
  exact And.intro valueEmpty
    (And.intro selfEmpty
      (And.intro inverseEmpty
        (And.intro selfUnary (And.intro inverseUnary L.identityRow))))

end BEDC.Derived.ManifoldUp
