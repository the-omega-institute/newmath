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

theorem NetworkFlow_cut_accounting_suffix_cancellation
    {V cutBack cutForw internal left right : BHist} :
    hsame left (append cutBack internal) -> hsame right (append cutForw internal) ->
      Cont V left right -> Cont V cutBack cutForw := by
  intro sameLeft sameRight accounting
  have transported :
      Cont V (append cutBack internal) (append cutForw internal) :=
    cont_hsame_transport (hsame_refl V) sameLeft sameRight accounting
  exact cont_suffix_iff.mp transported

end BEDC.Derived.NetworkFlowUp
