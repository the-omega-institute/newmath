import BEDC.Derived.ProbSpaceUp

namespace BEDC.Derived.HypothesisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.Cont
open BEDC.Derived.PreorderUp
open BEDC.Derived.ProbSpaceUp

theorem HypothesisDecisionCarrier_type_one_error_ledger
    {nullBound rejectEvent complement errorBudget : BHist} :
    ProbSpacePublicEventPacket nullBound errorBudget rejectEvent complement errorBudget ->
      hsame complement BHist.Empty ->
        hsame nullBound errorBudget ∧ hsame rejectEvent errorBudget ∧
          PreorderPrefixLE rejectEvent errorBudget ∧ UnaryHistory rejectEvent ∧
            UnaryHistory errorBudget := by
  intro packet complementEmpty
  have bounds :
      hsame errorBudget errorBudget ∧ UnaryHistory errorBudget ∧
        Cont rejectEvent complement errorBudget ∧ PreorderPrefixLE rejectEvent errorBudget :=
    ProbSpacePublicEventPacket_normalization_bounds packet
  have rejectBudget : hsame rejectEvent errorBudget := by
    have rejectToSelf : Cont rejectEvent BHist.Empty rejectEvent := cont_right_unit rejectEvent
    have rejectWithEmptyComplement : Cont rejectEvent BHist.Empty errorBudget :=
      cont_hsame_transport (hsame_refl rejectEvent) complementEmpty
        (hsame_refl errorBudget) bounds.right.right.left
    exact cont_deterministic rejectToSelf rejectWithEmptyComplement
  exact And.intro packet.right.right.right.left
    (And.intro rejectBudget
      (And.intro bounds.right.right.right
        (And.intro packet.left bounds.right.left)))

end BEDC.Derived.HypothesisUp
