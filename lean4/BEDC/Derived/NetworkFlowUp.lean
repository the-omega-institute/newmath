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

theorem NetworkFlow_weak_duality_cuts {V B X U : BHist} :
    UnaryHistory B -> Cont V B X -> PreorderPrefixLE X U -> PreorderPrefixLE V U := by
  intro backwardUnary accounting cutBound
  have accountingBound : PreorderPrefixLE V X := ⟨B, backwardUnary, accounting⟩
  exact PreorderPrefixLE_trans accountingBound cutBound

end BEDC.Derived.NetworkFlowUp
