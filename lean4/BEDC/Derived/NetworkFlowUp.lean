import BEDC.Derived.PreorderUp

namespace BEDC.Derived.NetworkFlowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.PreorderUp

theorem NetworkFlow_empty_backward_accounting_cut_flow_below_value {V B X : BHist} :
    UnaryHistory B -> hsame B BHist.Empty -> Cont V B X -> PreorderPrefixLE X V := by
  intro _backwardUnary backwardEmpty accounting
  cases backwardEmpty
  have sameXV : hsame X V := cont_deterministic accounting (cont_right_unit V)
  exact PreorderPrefixLE_of_hsame sameXV

theorem NetworkFlow_residual_exhaustion_cut_value_hsame {V B X K : BHist} :
    UnaryHistory B -> hsame B BHist.Empty -> Cont V B X -> PreorderPrefixLE V K ->
      PreorderPrefixLE K X -> hsame V K ∧ PreorderPrefixLE V K ∧ PreorderPrefixLE K V := by
  intro backwardUnary backwardEmpty accounting valueBelowCut cutBelowExhausted
  have exhaustedBelowValue : PreorderPrefixLE X V :=
    NetworkFlow_empty_backward_accounting_cut_flow_below_value backwardUnary backwardEmpty accounting
  have cutBelowValue : PreorderPrefixLE K V :=
    PreorderPrefixLE_trans cutBelowExhausted exhaustedBelowValue
  exact And.intro (PreorderPrefixLE_antisymm_hsame valueBelowCut cutBelowValue)
    (And.intro valueBelowCut cutBelowValue)

end BEDC.Derived.NetworkFlowUp
