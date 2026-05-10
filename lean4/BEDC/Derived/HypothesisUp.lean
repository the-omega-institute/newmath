import BEDC.Derived.ProbSpaceUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.HypothesisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
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

theorem HypothesisTestDecisionCarrier_type_one_error_ledger
    {null reject budget ledger endpoint : BHist} :
    UnaryHistory null -> UnaryHistory reject -> UnaryHistory budget ->
      Cont reject budget ledger -> Cont null ledger endpoint ->
        UnaryHistory ledger ∧ UnaryHistory endpoint ∧ hsame ledger (append reject budget) ∧
          hsame endpoint (append null ledger) := by
  intro nullUnary rejectUnary budgetUnary ledgerRow endpointRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed rejectUnary budgetUnary ledgerRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed nullUnary ledgerUnary endpointRow
  exact ⟨ledgerUnary, endpointUnary, ledgerRow, endpointRow⟩

theorem HypothesisTestDecisionCarrier_distribution_boundary
    {null alternative sample statistic threshold decision nullLedger altLedger surface : BHist} :
    UnaryHistory null -> UnaryHistory alternative -> UnaryHistory sample -> UnaryHistory statistic ->
      UnaryHistory threshold -> Cont sample statistic decision -> Cont decision threshold nullLedger ->
        Cont alternative threshold altLedger -> Cont nullLedger altLedger surface ->
          UnaryHistory decision ∧ UnaryHistory nullLedger ∧ UnaryHistory altLedger ∧
            UnaryHistory surface ∧ hsame decision (append sample statistic) ∧
              hsame nullLedger (append decision threshold) ∧
                hsame altLedger (append alternative threshold) ∧
                  hsame surface (append nullLedger altLedger) := by
  intro nullUnary alternativeUnary sampleUnary statisticUnary thresholdUnary decisionRow
    nullLedgerRow altLedgerRow surfaceRow
  have decisionUnary : UnaryHistory decision :=
    unary_cont_closed sampleUnary statisticUnary decisionRow
  have nullLedgerUnary : UnaryHistory nullLedger :=
    unary_cont_closed decisionUnary thresholdUnary nullLedgerRow
  have altLedgerUnary : UnaryHistory altLedger :=
    unary_cont_closed alternativeUnary thresholdUnary altLedgerRow
  have surfaceUnary : UnaryHistory surface :=
    unary_cont_closed nullLedgerUnary altLedgerUnary surfaceRow
  exact
    ⟨decisionUnary, nullLedgerUnary, altLedgerUnary, surfaceUnary, decisionRow, nullLedgerRow,
      altLedgerRow, surfaceRow⟩

end BEDC.Derived.HypothesisUp
