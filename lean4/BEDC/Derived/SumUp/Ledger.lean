import BEDC.Derived.SumUp

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist

def SumHistoryLedgerPolicy (Left Right : BHist -> Prop) (raw visible : BHist) : Prop :=
  SumHistoryCarrier Left Right raw ∧ hsame raw visible

theorem SumHistoryLedgerPolicy_visible_carrier {Left Right : BHist -> Prop}
    {raw visible : BHist} :
    SumHistoryLedgerPolicy Left Right raw visible -> SumHistoryCarrier Left Right visible := by
  intro ledger
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      exact SumHistoryCarrier_hsame_transport sameRawVisible rawCarrier

end BEDC.Derived.SumUp
